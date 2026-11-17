defmodule Lynx.Rust.SliceModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  def resolve(function, translated, refs),
    do: copy(function, translated, refs) || slice(function, translated, refs)

  defp copy(function, translated, refs) do
    variable = %{"TypeVar" => %{"Free" => 0}}
    slice = %{"Slice" => [variable, nil]}
    reference = fn index, kind -> %{"Ref" => [%{"Var" => %{"Free" => index}}, slice, kind]} end

    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => raw,
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig
         } <- function,
         true <- inherent?(function["item_meta"]["name"], slice, refs, "copy_from_slice"),
         params = CallModels.expand(raw, refs),
         true <- Enum.map(params["regions"], & &1["index"]) == [0, 1],
         [%{"index" => 0}] <- params["types"],
         true <- params["const_generics"] == [] and params["trait_type_constraints"] == [],
         [
           %{
             "clause_id" => 0,
             "trait_" => %{
               "regions" => [],
               "outlives" => [],
               "skip_binder" => %{"id" => trait, "generics" => args}
             }
           }
         ] <- params["trait_clauses"],
         true <- args == arguments([variable]),
         [decl] <- Enum.filter(translated["trait_decls"] || [], &(&1 && &1["def_id"] == trait)),
         true <-
           decl["item_meta"]["name"] == Enum.map(~w(core marker Copy), &%{"Ident" => [&1, 0]}) and
             decl["item_meta"]["lang_item"] == "Copy",
         true <-
           decl["src"] == "Normal" and decl["is_unsafe"] == false and
             Enum.all?(~w(methods consts types), &(decl[&1] == [])),
         true <-
           params["outlives"] ==
             Enum.map([0, 1], fn index ->
               %{
                 "regions" => [],
                 "outlives" => [],
                 "skip_binder" => [%{"Lub" => variable}, %{"Var" => %{"Free" => index}}]
               }
             end),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             reference.(0, "Mut"),
             reference.(1, "Shared")
           ],
         true <- tuple?(CallModels.expand(sig["output"], refs), []) do
      model("core::slice::{[@T]}::copy_from_slice", "Aeneas.Std.core.slice.Slice.copy_from_slice")
      |> Map.put(
        :label,
        "Upstream Copy slice model: equal-length copying replaces every destination element; length mismatch panics; the canonical Copy marker has no callbacks; Rust core and native memory layout remain unverified"
      )
    else
      _ -> nil
    end
  end

  defp slice(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "signature" => %{"is_unsafe" => false, "abi" => "Rust", "is_variadic" => false} = sig,
           "generics" => params
         } <- function,
         true <- parameters?(CallModels.expand(params, refs)) do
      t = %{"TypeVar" => %{"Free" => 0}}
      slice = %{"Slice" => [t, nil]}
      shared = %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Shared"]}
      mutable = %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Mut"]}
      usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
      inputs = CallModels.expand(sig["inputs"], refs)
      output = CallModels.expand(sig["output"], refs)
      name = function["item_meta"]["name"]
      range = range_operation(function, translated, refs, t, slice, usize, shared, inputs, output)

      cond do
        range != nil ->
          range

        inherent?(name, slice, refs, "first") and inputs == [shared] and
          option_reference?(output, t, translated, refs) and function["src"] == "Normal" ->
          model("core::slice::{[@T]}::first", "SliceModel.first")
          |> Map.merge(%{
            builtin: false,
            can_fail: true,
            lift: true,
            slice_first: true,
            label:
              "Standard shared slice first model using the existing checked index-zero primitive; empty slices return None; native Rust implementation, pointer metadata/layout and borrowing correspondence remain unverified"
          })

        inherent?(name, slice, refs, "is_empty") and inputs == [shared] and
          output == %{"Scalar" => "Bool"} and function["src"] == "Normal" ->
          model("core::slice::{[@T]}::is_empty", "Aeneas.Std.core.slice.Slice.is_empty")
          |> Map.put(:lift, false)

        inherent?(name, slice, refs) and inputs == [shared, usize] and
          tuple?(output, [shared, shared]) and function["src"] == "Normal" ->
          model("core::slice::{[@T]}::split_at", "Aeneas.Std.core.slice.Slice.split_at")

        inputs == [usize, shared] and option_reference?(output, t, translated, refs) and
            index_identity?(function, translated, refs, t, slice, usize, "get", 0) ->
          model(
            "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get",
            "Aeneas.Std.core.slice.index.Usize.get"
          )
          |> Map.put(:can_fail, false)

        inputs == [usize, shared] and
          output == %{"Ref" => [%{"Var" => %{"Free" => 0}}, t, "Shared"]} and
            index_identity?(function, translated, refs, t, slice, usize, "index", 4) ->
          model(
            "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index",
            "Aeneas.Std.core.slice.index.Usize.index"
          )

        inputs == [usize, mutable] and
          output == %{"Ref" => [%{"Var" => %{"Free" => 0}}, t, "Mut"]} and
            index_identity?(function, translated, refs, t, slice, usize, "index_mut", 5) ->
          model(
            "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index_mut",
            "Aeneas.Std.core.slice.index.Usize.index_mut"
          )

        true ->
          nil
      end
    else
      _ -> nil
    end
  end

  defp option_reference?(
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}},
         t,
         translated,
         refs
       ) do
    type = Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id))

    type != nil and Lynx.Rust.OptionModels.option_type?(type, refs) and
      args == arguments([%{"Ref" => [%{"Var" => %{"Free" => 0}}, t, "Shared"]}])
  end

  defp option_reference?(_, _, _, _), do: false

  defp model(rust, lean),
    do: %{
      rust_name: rust,
      lean: lean,
      builtin: true,
      can_fail: true,
      lift: true,
      label:
        "Aeneas safe slice model preserving bounds panics and mutable updates; Rust core implementation not verified"
    }

  defp parameters?(%{
         "regions" => [%{"index" => 0}],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "trait_type_constraints" => [],
         "outlives" => outlives
       }),
       do:
         outlives in [
           [],
           [
             %{
               "regions" => [],
               "outlives" => [],
               "skip_binder" => [
                 %{"Lub" => %{"TypeVar" => %{"Free" => 0}}},
                 %{"Var" => %{"Free" => 0}}
               ]
             }
           ]
         ]

  defp parameters?(_), do: false

  defp inherent?(name, slice, refs, method \\ "split_at")

  defp inherent?(
         [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["slice", 0]},
           %{"Impl" => %{"Ty" => %{"skip_binder" => parent}}},
           %{"Ident" => [method, 0]}
         ],
         slice,
         refs,
         method
       ) do
    parent |> CallModels.expand(refs) |> free() == slice
  end

  defp inherent?(_, _, _, _), do: false

  defp free(%{"Bound" => [0, index]}), do: %{"Free" => index}
  defp free(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free(v)} end)
  defp free(list) when is_list(list), do: Enum.map(list, &free/1)
  defp free(value), do: value

  defp tuple?(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}, fields),
    do: args == arguments(fields)

  defp tuple?(_, _), do: false

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp index_identity?(
         function,
         translated,
         refs,
         t,
         slice,
         index,
         method_name,
         method_index,
         output \\ nil
       ) do
    output = output || t
    id = function["def_id"]

    with %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => impl_id, "generics" => impl_args},
             "trait_ref" => %{"id" => trait, "generics" => trait_args},
             "item_id" => ^method_index,
             "reuses_default" => false
           }
         } <- function["src"],
         impl when not is_nil(impl) <-
           Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         decl when not is_nil(decl) <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == trait)) do
      name = [%{"Ident" => ["core", 0]}, %{"Ident" => ["slice", 0]}, %{"Ident" => ["index", 0]}]

      function["item_meta"]["name"] ==
        name ++ [%{"Impl" => %{"Trait" => impl_id}}, %{"Ident" => [method_name, 0]}] and
        decl["item_meta"]["name"] == name ++ [%{"Ident" => ["SliceIndex", 0]}] and
        impl["src"] == "Normal" and impl["is_negative"] == false and
        impl["is_unsafe"] == true and decl["is_unsafe"] == true and
        impl["types"] == [nil] and impl["consts"] == [] and impl["implied_trait_refs"] == [] and
        impl_parameters?(impl["generics"]) and
        CallModels.expand(impl_args, refs) == arguments([t]) and
        CallModels.expand(trait_args, refs) == arguments([index, slice, output]) and
        CallModels.expand(impl["impl_trait"], refs) == %{
          "id" => trait,
          "generics" => arguments([index, slice, output])
        } and
        case Enum.filter(
               impl["methods"],
               &(&1["kind"] == %{"TraitMethod" => [trait, method_index]})
             ) do
          [%{"params" => method_params, "skip_binder" => %{"id" => ^id, "generics" => args}}] ->
            method_parameters?(method_params) and
              CallModels.expand(args, refs) ==
                Map.put(arguments([t]), "regions", [%{"Var" => %{"Bound" => [0, 0]}}])

          _ ->
            false
        end
    else
      _ -> false
    end
  end

  # Retain and check the compiler's actual nominal range definition. The model
  # is selected by structure and identity, never by a user type's short name.
  defp range_operation(function, translated, refs, t, slice, usize, shared, inputs, output) do
    operation =
      cond do
        option_reference?(output, slice, translated, refs) -> {"get", 0}
        output == %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Shared"]} -> {"index", 4}
        output == %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Mut"]} -> {"index_mut", 5}
        true -> nil
      end

    if operation do
      {method, method_index} = operation

      Enum.find_value(
        [{"RangeTo", ["end"]}, {"RangeFrom", ["start"]}, {"Range", ["start", "end"]}],
        fn {kind, fields} ->
          index = range_type(translated, refs, usize, kind, fields)

          reference =
            if method == "index_mut",
              do: %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Mut"]},
              else: shared

          if index != nil and
               inputs == [index, reference] and
               index_identity?(
                 function,
                 translated,
                 refs,
                 t,
                 slice,
                 index,
                 method,
                 method_index,
                 slice
               ) do
            model(
              "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::#{kind}<usize>, [@T], [@T]>}::#{method}",
              "Aeneas.Std.core.slice.index.SliceIndex#{kind}UsizeSlice.#{method}"
            )
            |> Map.put(
              :label,
              "Aeneas safe slice model for #{kind}::#{method}; " <>
                if(method == "get",
                  do: "invalid bounds return None",
                  else: "invalid bounds panic"
                ) <>
                "; Rust core implementation not verified"
            )
            |> checked_range_from(kind, method)
          end
        end
      )
    end
  end

  # Upstream's shared RangeFrom index returns undef outside bounds. Override
  # both the direct function and its dictionary field with the checked model.
  defp checked_range_from(model, "RangeFrom", "index"),
    do:
      model
      |> Map.put(:builtin, false)
      |> Map.put(:slice_range_from_checked, true)
      |> Map.put(
        :label,
        "Checked shared RangeFrom indexing adapter and dictionary: reuse upstream valid slicing, preserve Rust bounds panics instead of upstream undef; nominal type IDs/fields retained under a backend alias; Rust core and native memory layout remain unverified"
      )

  defp checked_range_from(model, _, _), do: model

  def scope(audit, prefix) do
    %{
      audit
      | external_calls:
          Map.new(audit.external_calls, fn {id, model} ->
            cond do
              model[:slice_range_from_checked] ->
                {id, %{model | lean: prefix <> ".SliceModel.indexFrom"}}

              model[:slice_first] ->
                {id, %{model | lean: prefix <> ".SliceModel.first"}}

              true ->
                {id, model}
            end
          end)
    }
  end

  # An available but uncalled shared index must retain the packaged dictionary:
  # otherwise a File-only extraction would rename RangeFrom without installing
  # the checked shared-index dictionary. Called models always use scoped names.
  def backend_calls(available, called) do
    available
    |> Map.reject(fn {id, model} ->
      (model[:slice_range_from_checked] == true or model[:slice_first] == true) and
        not Map.has_key?(called, id)
    end)
    |> Map.merge(called)
  end

  # Alias only the already audited standard range type, retaining its ID,
  # fields and generic arguments. ExternalNames deliberately forbids overriding
  # a packaged model; the distinct backend name selects the checked dictionary.
  def lower_names!(document, calls) do
    if Enum.any?(calls, fn {_, m} -> m[:slice_range_from_checked] end) do
      original = Enum.map(~w(core ops range RangeFrom), &%{"Ident" => [&1, 0]})
      renamed = Enum.map(~w(lynx_slice RangeFrom), &%{"Ident" => [&1, 0]})
      types = document["translated"]["type_decls"]
      [type] = Enum.filter(types, &(&1 && &1["item_meta"]["name"] == original))
      type_id = type["def_id"]

      if Enum.any?(types, &(&1 && &1["item_meta"]["name"] == renamed)),
        do: raise(ArgumentError, "checked slice range model name collides with another type")

      document =
        put_in(
          document,
          ["translated", "type_decls"],
          Enum.map(types, fn
            %{"def_id" => ^type_id} = item ->
              put_in(item, ["item_meta", "name"], renamed)

            item ->
              item
          end)
        )

      calls =
        Map.new(calls, fn {id, model} ->
          if String.contains?(model.rust_name, "core::ops::range::RangeFrom<usize>") do
            {id,
             model
             |> Map.put(:builtin, false)
             |> Map.put(
               :backend_rust_name,
               String.replace(
                 model.rust_name,
                 "core::ops::range::RangeFrom<usize>",
                 "lynx_slice::RangeFrom<usize>"
               )
             )}
          else
            {id, model}
          end
        end)

      impls =
        calls
        |> Map.values()
        |> Enum.filter(& &1[:slice_range_from_checked])
        |> Enum.map(&get_in(&1, [:function, "src", "TraitImpl", "impl_ref", "id"]))
        |> Enum.uniq()

      functions = document["translated"]["fun_decls"]

      omitted =
        for function <- functions,
            function,
            function["body"] == "Opaque",
            source_impl(function["src"]) in impls,
            not Map.has_key?(calls, function["def_id"]),
            do: function["def_id"]

      used =
        (functions |> Enum.reject(&is_nil/1) |> Enum.flat_map(&function_refs(&1["body"]))) ++
          function_refs(document["translated"]["global_decls"])

      unless Enum.all?(omitted, &(&1 not in used)),
        do: raise(ArgumentError, "unmodelled slice dictionary member is called")

      document =
        put_in(
          document,
          ["translated", "fun_decls"],
          Enum.map(functions, fn function ->
            if function && function["def_id"] in omitted, do: nil, else: function
          end)
        )

      document =
        update_in(document, ["translated", "ordered_decls"], fn groups ->
          Enum.flat_map(groups, fn
            %{"Fun" => %{"NonRec" => id}} = group ->
              if id in omitted, do: [], else: [group]

            %{"Fun" => %{"Rec" => ids}} ->
              case ids -- omitted do
                [] -> []
                kept -> [%{"Fun" => %{"Rec" => kept}}]
              end

            group ->
              [group]
          end)
        end)

      {document,
       [
         %{
           type_id: type["def_id"],
           original: original,
           renamed: renamed,
           omitted_unreferenced_functions: omitted
         }
       ], calls}
    else
      {document, [], calls}
    end
  end

  defp source_impl(%{"TraitImpl" => %{"impl_ref" => %{"id" => id}}}), do: id
  defp source_impl(_), do: nil

  defp function_refs(%{"Fun" => id}) when is_integer(id), do: [id]
  defp function_refs(node) when is_map(node), do: function_refs(Map.values(node))
  defp function_refs(nodes) when is_list(nodes), do: Enum.flat_map(nodes, &function_refs/1)
  defp function_refs(_), do: []

  def external_names(calls, prefix) do
    if Enum.any?(calls, fn {_, model} -> model[:slice_range_from_checked] end) do
      %{
        "types" => [
          %{
            "rust_pattern" => "lynx_slice::RangeFrom",
            "extract_name" => "Aeneas.Std.core.ops.range.RangeFrom"
          }
        ],
        "trait_impls" => [
          %{
            "rust_pattern" =>
              "core::slice::index::SliceIndex<lynx_slice::RangeFrom<usize>, [@T], [@T]>",
            "extract_name" => prefix <> ".SliceModel.rangeFrom"
          }
        ]
      }
    else
      %{}
    end
  end

  def install!(audit, output, prefix) do
    if Enum.any?(audit.external_calls, fn {_, model} ->
         model[:slice_range_from_checked] == true or model[:slice_first] == true
       end) do
      module = prefix <> ".SliceModel"
      path = Path.join(output, String.replace(module, ".", "/") <> ".lean")

      case File.read(path) do
        {:ok, "-- Generated by Lynx: bounds-checked shared slice indexing.\n" <> _} -> :ok
        {:error, :enoent} -> :ok
        _ -> raise(ArgumentError, "refusing to overwrite a user slice model module: #{path}")
      end

      File.mkdir_p!(Path.dirname(path))

      File.write!(path, """
      -- Generated by Lynx: bounds-checked shared slice indexing.
      module
      public import Aeneas
      public section
      open Aeneas Aeneas.Std
      namespace #{module}
      @[expose] def first {T : Type} (input : Slice T) : RustM (Option T) :=
        core.slice.index.Usize.get 0#usize input
      theorem first_empty {T : Type} (input : Slice T) (empty : input.val = []) : first input = RustM.ok none := by
        simp [first, core.slice.index.Usize.get, empty]
      @[expose] def indexFrom {T : Type} (range : core.ops.range.RangeFrom Usize) (input : Slice T) : RustM (Slice T) :=
        if range.start.val ≤ input.length then core.slice.index.SliceIndexRangeFromUsizeSlice.index range input
        else RustM.fail .panic
      @[expose] def rangeFrom (T : Type) : core.slice.index.SliceIndex (core.ops.range.RangeFrom Usize) (Slice T) (Slice T) :=
        {core.slice.index.SliceIndexRangeFromUsizeSlice T with index := indexFrom}
      theorem indexFrom_valid {T : Type} (range : core.ops.range.RangeFrom Usize) (input : Slice T)
          (valid : range.start.val ≤ input.length) : indexFrom range input = RustM.ok (input.drop range.start) := by
        simp [indexFrom,valid,core.slice.index.SliceIndexRangeFromUsizeSlice.index]
      theorem indexFrom_invalid {T : Type} (range : core.ops.range.RangeFrom Usize) (input : Slice T)
          (invalid : ¬range.start.val ≤ input.length) : indexFrom range input = RustM.fail .panic := by
        simp [indexFrom,invalid]
      end #{module}
      """)

      funs = Path.join(output, String.replace(prefix, ".", "/") <> "/Funs.lean")
      source = File.read!(funs)
      marker = "public import " <> prefix <> ".Types"

      unless String.contains?(source, marker),
        do: raise(ArgumentError, "missing generated slice Types import")

      File.write!(funs, String.replace(source, marker, marker <> "\npublic import " <> module))
      [module]
    else
      []
    end
  end

  defp range_type(translated, refs, usize, kind, expected_fields) do
    Enum.find_value(translated["type_decls"], fn
      %{
        "def_id" => id,
        "src" => "Normal",
        "item_meta" => %{"name" => name},
        "generics" => params,
        "kind" => %{"Struct" => fields}
      }
      when is_list(fields) ->
        if name == Enum.map(["core", "ops", "range", kind], &%{"Ident" => [&1, 0]}) and
             impl_parameters?(params) and Enum.map(fields, & &1["name"]) == expected_fields and
             Enum.all?(
               fields,
               &(CallModels.expand(&1["ty"], refs) == %{"TypeVar" => %{"Free" => 0}})
             ) do
          %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments([usize])}}
        end

      _ ->
        nil
    end)
  end

  defp impl_parameters?(%{
         "regions" => [],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "outlives" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp impl_parameters?(_), do: false

  defp method_parameters?(%{
         "regions" => [%{"index" => 0}],
         "types" => [],
         "const_generics" => [],
         "trait_clauses" => [],
         "outlives" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp method_parameters?(_), do: false
end
