defmodule Lynx.Rust.AtomicModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, ResourceModels}
  @base ~w(core sync atomic)
  @variants ~w(Relaxed Release Acquire AcqRel SeqCst)
  @u64 %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}

  def type?(%{"kind" => "Opaque", "item_meta" => %{"name" => name}, "generics" => params}),
    do: name == path(@base ++ ["Atomic"]) and params?(params, 2, 0)

  def type?(_), do: false

  def supported?(type, translated, refs) do
    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} ->
        declaration = find(translated["type_decls"], id)

        with true <- type?(declaration),
             %{"types" => [value, storage]} <- args,
             true <- args == ResourceModels.args([value, storage]),
             true <- CallModels.expand(value, refs) == @u64,
             %{"Adt" => %{"id" => storage_id, "builtin" => nil, "generics" => storage_args}} <-
               CallModels.expand(storage, refs),
             true <- storage_args == ResourceModels.args([value]),
             %{"kind" => "Opaque", "item_meta" => %{"name" => name}, "generics" => params} <-
               find(translated["type_decls"], storage_id),
             true <- name == path(@base ++ ["private", "Align8"]),
             true <- params?(params, 1, 0) do
          %{atomic: id, storage: storage_id}
        else
          _ -> nil
        end

      _ ->
        nil
    end
  end

  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => params,
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "item_meta" => %{
             "name" => [a, b, c, %{"Impl" => %{"Ty" => parent}}, %{"Ident" => [method, 0]}]
           }
         } <- function,
         true <- [a, b, c] == path(@base),
         true <- method in ~w(load store fetch_add),
         %{"kind" => "InherentImplBlock", "params" => parent_params, "skip_binder" => self} <-
           parent,
         true <- params?(parent_params, 0, 0),
         %{atomic: atomic, storage: storage} <- supported?(self, translated, refs),
         self <- CallModels.expand(self, refs),
         ordering when not is_nil(ordering) <- ordering(translated),
         true <- params?(params, 0, 1),
         true <- signature?(method, sig, self, ordering["def_id"], refs) do
      %{
        rust_name:
          "core::sync::atomic::{core::sync::atomic::Atomic<u64,core::sync::atomic::private::Align8<u64>>}::#{method}",
        lean: "Lynx.NativeAtomic.#{if method == "fetch_add", do: "fetchAdd", else: method}",
        builtin: false,
        can_fail: true,
        lift: true,
        native_cutoff_only: true,
        native_atomic_type: atomic,
        native_atomic_storage_type: storage,
        native_atomic_ordering_type: ordering["def_id"],
        label:
          "Sequentially consistent AtomicU64 #{method} model: shared typed identity and atomic state transition; fetch_add wraps at 64 bits and returns the prior value; only SeqCst construction and shared borrowing are admitted; Rust core, hardware memory ordering, allocation and FFI remain unverified"
      }
    else
      _ -> nil
    end
  end

  defp signature?(method, sig, self, ordering, refs) do
    order = %{
      "Adt" => %{"id" => ordering, "builtin" => nil, "generics" => ResourceModels.args([])}
    }

    borrowed = %{"Ref" => [%{"Var" => %{"Free" => 0}}, self, "Shared"]}

    {inputs, output} =
      case method do
        "load" -> {[borrowed, order], @u64}
        "store" -> {[borrowed, @u64, order], unit()}
        "fetch_add" -> {[borrowed, @u64, order], @u64}
      end

    CallModels.expand(sig["inputs"], refs) == inputs and
      CallModels.expand(sig["output"], refs) == output
  end

  defp ordering(translated) do
    Enum.find(translated["type_decls"], fn type ->
      type && type["item_meta"]["name"] == path(@base ++ ["Ordering"]) &&
        params?(type["generics"], 0, 0) &&
        match?(%{"Enum" => _}, type["kind"]) &&
        Enum.map(type["kind"]["Enum"], & &1["name"]) == @variants &&
        Enum.all?(Enum.with_index(type["kind"]["Enum"]), fn {variant, index} ->
          variant["id"] == index and variant["fields"] == []
        end)
    end)
  end

  def audit!(functions, models, translated, refs) do
    if Enum.any?(models, fn {_, model} -> model[:native_atomic_type] end) do
      order = ordering(translated)
      seq_cst = Enum.find(order["kind"]["Enum"], &(&1["name"] == "SeqCst"))["id"]

      # Owning cells require explicit lifetime/codec support. This initial model
      # admits only shared references to the exact compiler-validated U64 type.
      for type <- translated["type_decls"], type != nil, is_map(type["kind"]) do
        if contains_order?(type["kind"], order["def_id"], refs) or
             contains_atomic?(type["kind"], translated, refs),
           do:
             raise(
               ArgumentError,
               "atomic cells and ordering values in aggregate fields are unsupported"
             )
      end

      for global <- translated["global_decls"], global != nil do
        if contains_order?(global, order["def_id"], refs) or
             contains_atomic?(global, translated, refs),
           do: raise(ArgumentError, "global atomic cells and ordering values are unsupported")
      end

      for function <- functions do
        if contains_order?(function["signature"], order["def_id"], refs) or
             contains_order?(function["generics"], order["def_id"], refs),
           do:
             LLBC.failure!(
               function,
               translated,
               "atomic ordering parameters and results are unsupported; use an explicit Ordering::SeqCst"
             )

        audit_types!(function["signature"], function, translated, refs)

        if locals = get_in(function, ["body", "Structured", "locals", "locals"]) do
          for local <- locals, do: audit_types!(local["ty"], function, translated, refs)
        end

        audit_body!(function["body"], order["def_id"], seq_cst, function, translated, refs)
      end
    end

    :ok
  end

  defp audit_body!(
         %{"Aggregate" => [%{"Adt" => [%{"id" => id}, variant, _]}, _]},
         id,
         seq,
         function,
         translated,
         _
       ) do
    if variant != seq,
      do:
        LLBC.failure!(
          function,
          translated,
          "only Ordering::SeqCst is supported; weaker memory orderings require a separate memory model"
        )
  end

  defp audit_body!(map, id, seq, function, translated, refs) when is_map(map),
    do: Enum.each(Map.values(map), &audit_body!(&1, id, seq, function, translated, refs))

  defp audit_body!(list, id, seq, function, translated, refs) when is_list(list),
    do: Enum.each(list, &audit_body!(&1, id, seq, function, translated, refs))

  defp audit_body!(_, _, _, _, _, _), do: :ok

  defp contains_order?(type, id, refs) do
    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => ^id}} -> true
      map when is_map(map) -> Enum.any?(Map.values(map), &contains_order?(&1, id, refs))
      list when is_list(list) -> Enum.any?(list, &contains_order?(&1, id, refs))
      _ -> false
    end
  end

  defp contains_atomic?(value, translated, refs) do
    value = CallModels.expand(value, refs)

    case value do
      %{"Adt" => %{"id" => id, "builtin" => nil}} ->
        type?(find(translated["type_decls"], id)) or children_atomic?(value, translated, refs)

      _ ->
        children_atomic?(value, translated, refs)
    end
  end

  defp children_atomic?(map, translated, refs) when is_map(map),
    do: Enum.any?(Map.values(map), &contains_atomic?(&1, translated, refs))

  defp children_atomic?(list, translated, refs) when is_list(list),
    do: Enum.any?(list, &contains_atomic?(&1, translated, refs))

  defp children_atomic?(_, _, _), do: false

  defp audit_types!(value, function, translated, refs) do
    case CallModels.expand(value, refs) do
      %{"Ref" => [_, inner, "Shared"]} = value ->
        if supported?(inner, translated, refs) do
          :ok
        else
          audit_type_children!(value, function, translated, refs)
        end

      %{"Adt" => %{"id" => id, "builtin" => nil}} = value ->
        if type?(find(translated["type_decls"], id)),
          do:
            LLBC.failure!(
              function,
              translated,
              "only shared borrows of AtomicU64 are supported; owned cells, other widths and storage layouts require separate models"
            )

        audit_type_children!(value, function, translated, refs)

      value ->
        audit_type_children!(value, function, translated, refs)
    end
  end

  defp audit_type_children!(map, function, translated, refs) when is_map(map),
    do: Enum.each(Map.values(map), &audit_types!(&1, function, translated, refs))

  defp audit_type_children!(list, function, translated, refs) when is_list(list),
    do: Enum.each(list, &audit_types!(&1, function, translated, refs))

  defp audit_type_children!(_, _, _, _), do: :ok

  def type_models(models, prefix) do
    if Enum.any?(models, fn {_, model} -> model[:native_atomic_type] end) do
      module = hd(String.split(prefix, ".")) <> ".NativeRuntime"

      [
        %{
          rust: "core::sync::atomic::Atomic",
          lean: "Lynx.NativeAtomic",
          import: module,
          label:
            "Typed atomic identity; only validated Atomic<u64, Align8<u64>> instantiations are supported"
        },
        %{
          rust: "core::sync::atomic::private::Align8",
          lean: "Lynx.NativeAtomicStorage",
          import: module,
          label: "Phantom atomic storage alignment; physical Rust layout remains unverified"
        },
        %{
          rust: "core::sync::atomic::Ordering",
          lean: "Lynx.NativeAtomicOrdering",
          import: module,
          body: %{
            "kind" => "enum",
            "variants" => Enum.map(@variants, &%{"rust" => &1, "extract" => &1})
          },
          label: "Compiler-validated atomic Ordering variants; extraction admits SeqCst only"
        }
      ]
    else
      []
    end
  end

  defp unit,
    do: %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => ResourceModels.args([])}}

  defp find(values, id), do: Enum.find(values, &(&1 && &1["def_id"] == id))
  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})

  defp params?(params, types, regions) do
    match?(
      %{
        "types" => _,
        "regions" => _,
        "const_generics" => [],
        "trait_clauses" => [],
        "trait_type_constraints" => [],
        "outlives" => []
      },
      params
    ) and
      Enum.map(params["types"], & &1["index"]) ==
        if(types == 0, do: [], else: Enum.to_list(0..(types - 1))) and
      Enum.map(params["regions"], & &1["index"]) ==
        if(regions == 0, do: [], else: Enum.to_list(0..(regions - 1)))
  end
end
