defmodule Lynx.Rust.NativeDrops do
  @moduledoc false
  alias Lynx.Rust.{CallModels, MutexModels, LockModels, GuardDrops, ResourceModels, ResourceDrops}

  def resolve(function, translated, refs) do
    with true <- consuming_function?(function, translated, refs),
         mutex = Enum.find(translated["type_decls"], &(&1 && MutexModels.type?(&1))),
         guard = Enum.find(translated["type_decls"], &LockModels.guard?(&1, refs)),
         resource = Enum.find(translated["type_decls"], &ResourceModels.type?/1),
         true <- mutex != nil or guard != nil or resource != nil do
      %{
        rust_name: "core::mem::drop",
        lean:
          if(get_in(translated, ["options", "owned_drops"]) == true,
            do: "Lynx.NativeOwnedDrop.drop",
            else: "Lynx.NativeDrop.drop"
          ),
        builtin: false,
        can_fail: true,
        native_cutoff_only: true,
        lift: true,
        native_dispose: true,
        native_codec_drop: true,
        label:
          if(get_in(translated, ["options", "owned_drops"]) == true,
            do:
              "Consuming native destruction with validated nonpanicking structural resource payload cleanup linked to actual compiler drop MIR; mutex cell reclamation and resource owner retirement are atomic in the logical heap; observable final resource cleanup requires explicit synchronous timing or deferred callback dispatch, while unspecified timing exhausts verification; release acknowledgement does not imply callback completion; mutex and guard primitives, Rust std, allocation, VM callbacks and FFI remain modeled boundaries; custom resource destructor unwind unsupported",
            else:
              "Consuming destruction model: Mutex with a destructor-free payload atomically removes its own live unlocked cell of either poison status without overwriting unrelated native state; normal MutexGuard release commits its reconstructed payload and unlocks the owned cell without dropping the payload; Rust-owned ResourceArc atomically consumes one token and reclaims a destructor-free allocation on final release under default Resource callbacks; invalid identities exhaust verification; Rust std, allocation and FFI correctness unverified; guard unwind requires compiler-scoped captured cleanup; projected/custom payload destruction unsupported"
          )
      }
      |> then(fn model ->
        if mutex, do: Map.put(model, :native_mutex_type, mutex["def_id"]), else: model
      end)
      |> then(fn model ->
        if guard, do: Map.put(model, :native_guard_type, guard["def_id"]), else: model
      end)
      |> then(fn model ->
        if resource, do: Map.put(model, :native_resource_type, resource["def_id"]), else: model
      end)
    else
      _ -> nil
    end
  end

  def consuming_function?(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => params,
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "item_meta" => %{"name" => name}
         } <- function,
         true <- name == path(~w(core mem drop)),
         true <- parameters?(params),
         true <- CallModels.expand(sig["inputs"], refs) == [variable()],
         true <- unit?(CallModels.expand(sig["output"], refs)),
         [clause] <- params["trait_clauses"],
         true <- clause["clause_id"] == 0,
         %{
           "regions" => [],
           "outlives" => [],
           "skip_binder" => %{"id" => trait, "generics" => args}
         } <- clause["trait_"],
         true <- CallModels.expand(args, refs) == arguments([variable()]),
         true <- destruct?(trait, translated, refs) do
      true
    else
      _ -> false
    end
  end

  def needs_lowering?(document) do
    translated = document["translated"]
    refs = Lynx.Rust.LLBC.type_references!(document)
    Enum.any?(translated["fun_decls"], &(&1 && native_drop?(&1["body"], translated, refs)))
  end

  defp native_drop?(%{"Drop" => %{"place" => %{"ty" => type}}} = node, translated, refs) do
    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id}} ->
        Enum.any?(
          translated["type_decls"],
          &(&1 && &1["def_id"] == id &&
              (MutexModels.type?(&1) or LockModels.guard?(&1, refs) or ResourceModels.type?(&1) or
                 (Lynx.Rust.FileModels.file_type?(translated, id) or
                    Lynx.Rust.FileModels.error_type?(translated, id))))
        )

      _ ->
        Enum.any?(Map.values(node), &native_drop?(&1, translated, refs))
    end
  end

  defp native_drop?(map, translated, refs) when is_map(map),
    do: Enum.any?(Map.values(map), &native_drop?(&1, translated, refs))

  defp native_drop?(list, translated, refs) when is_list(list),
    do: Enum.any?(list, &native_drop?(&1, translated, refs))

  defp native_drop?(_, _, _), do: false

  def site(drop, translated, refs) do
    self = CallModels.expand(get_in(drop, ["place", "ty"]), refs)

    case self do
      %{"Adt" => %{"id" => id, "generics" => %{"types" => [payload]} = args}} ->
        type = Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id))

        cond do
          ResourceModels.type?(type) ->
            ResourceDrops.site(drop, translated, refs)

          LockModels.guard?(type, refs) ->
            GuardDrops.site(drop, translated, refs)

          type && MutexModels.type?(type) ->
            with true <-
                   (destructor_free?(payload, translated, refs) or
                      file_payload?(payload, translated, refs)) and args == arguments([payload]),
                 "Precise" <- drop["kind"],
                 %{"kind" => %{"Fun" => fid}, "generics" => call_args} <- drop["fn_ptr"],
                 %{
                   "regions" => [%{"Body" => region}],
                   "types" => [_],
                   "const_generics" => [],
                   "trait_refs" => []
                 } <- call_args,
                 true <- is_integer(region),
                 true <- CallModels.expand(call_args["types"], refs) == [payload],
                 function when not is_nil(function) <-
                   Enum.find(translated["fun_decls"], &(&1 && &1["def_id"] == fid)),
                 %{"TraitImpl" => source} <- function["src"],
                 impl_id = source["impl_ref"]["id"],
                 trait = source["trait_ref"]["id"],
                 true <- destruct?(trait, translated, refs),
                 impl when not is_nil(impl) <-
                   Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
                 true <- mutex_impl?(impl, id, trait, translated, refs),
                 [method] <- impl["methods"],
                 true <- method["skip_binder"]["id"] == fid do
              {:ok,
               %{
                 function: fid,
                 native_kind: :mutex,
                 impl: impl_id,
                 trait: trait,
                 payload: hd(call_args["types"]),
                 self: drop["place"]["ty"]
               }}
            else
              _ ->
                {:error,
                 "unsupported native drop payload or inconsistent compiler destructor; only compiler-certified destructor-free payloads or explicitly admitted owned File payloads are supported"}
            end

          true ->
            nil
        end

      %{"Adt" => %{"id" => id}} ->
        if Lynx.Rust.FileModels.file_type?(translated, id) or
             Lynx.Rust.FileModels.error_type?(translated, id),
           do: Lynx.Rust.FileDrops.site(drop, translated, refs),
           else: nil

      _ ->
        nil
    end
  end

  def audit(functions, models, translated, refs) do
    drops = for {id, model} <- models, model[:native_dispose], into: MapSet.new(), do: id

    translated =
      Map.put(
        translated,
        :native_file_drop,
        Enum.any?(models, fn {_, model} -> model[:native_file_drop] == true end)
      )

    if MapSet.size(drops) == 0 do
      :ok
    else
      trait_refs = collect_refs(translated, %{})

      Enum.reduce_while(functions, :ok, fn function, :ok ->
        try do
          inspect_calls!(function["body"], drops, translated, refs, trait_refs, false)
          {:cont, :ok}
        rescue
          error in ArgumentError -> {:halt, {:error, function, Exception.message(error)}}
        end
      end)
    end
  end

  defp inspect_calls!(
         %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => generics}},
         drops,
         translated,
         refs,
         traits,
         cleanup
       ) do
    if MapSet.member?(drops, id) do
      if cleanup,
        do: raise(ArgumentError, "native consuming calls during unwind are not yet translated")

      if not GuardDrops.call?(generics, translated, refs, traits) and
           not ResourceDrops.call?(generics, translated, refs, traits) and
           not (translated[:native_file_drop] &&
                  Lynx.Rust.FileDrops.call?(generics, translated, refs, traits)) do
        with %{
               "types" => [type],
               "regions" => [],
               "const_generics" => [],
               "trait_refs" => [dictionary]
             } <- generics,
             %{"Adt" => %{"id" => mutex, "builtin" => nil, "generics" => args}} = self <-
               CallModels.expand(type, refs),
             true <-
               Enum.any?(
                 translated["type_decls"],
                 &(&1 && &1["def_id"] == mutex && MutexModels.type?(&1))
               ),
             %{"types" => [payload], "regions" => [], "const_generics" => [], "trait_refs" => []} <-
               args,
             true <-
               destructor_free?(payload, translated, refs) or
                 (translated[:native_file_drop] == true and
                    file_payload?(payload, translated, refs)),
             %{"regions" => [], "outlives" => [], "skip_binder" => dictionary} <- dictionary,
             %{
               "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => impl_args}},
               "trait_decl_ref" => decl
             } <- expand_trait(dictionary, traits),
             true <- CallModels.expand(impl_args, refs) == arguments([payload]),
             true <- destruct?(decl["id"], translated, refs),
             true <- CallModels.expand(decl["generics"], refs) == arguments([self]),
             impl when not is_nil(impl) <-
               Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
             true <- mutex_impl?(impl, mutex, decl["id"], translated, refs) do
          :ok
        else
          _ ->
            raise ArgumentError,
                  "native destruction requires an explicitly admitted File or an exact Mutex, MutexGuard or default ResourceArc Destruct implementation with a compiler-certified destructor-free payload or explicitly admitted owned Mutex<File>; other custom payload destructors are unsupported"
        end
      end
    end
  end

  defp inspect_calls!(map, drops, translated, refs, traits, cleanup) when is_map(map),
    do:
      Enum.each(map, fn {key, value} ->
        inspect_calls!(
          value,
          drops,
          translated,
          refs,
          traits,
          cleanup or key in ["on_unwind", "on_failure"]
        )
      end)

  defp inspect_calls!(list, drops, translated, refs, traits, cleanup) when is_list(list),
    do: Enum.each(list, &inspect_calls!(&1, drops, translated, refs, traits, cleanup))

  defp inspect_calls!(_, _, _, _, _, _), do: :ok

  defp mutex_impl?(impl, mutex, trait, translated, refs) do
    self = %{"Adt" => %{"id" => mutex, "builtin" => nil, "generics" => arguments([variable()])}}

    expected_name =
      path(~w(std sync poison mutex Mutex)) ++ [%{"Impl" => %{"Trait" => impl["def_id"]}}]

    with %{
           "src" => "Destruct",
           "is_negative" => false,
           "is_unsafe" => false,
           "consts" => [],
           "types" => [],
           "implied_trait_refs" => [],
           "methods" => [method]
         } <- impl,
         true <- empty_parameters?(impl["generics"], 0, 1),
         true <- impl["item_meta"]["name"] == expected_name,
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait,
             "generics" => arguments([self])
           },
         true <- method["kind"] == %{"TraitMethod" => [trait, 0]},
         true <- empty_parameters?(method["params"], 1, 0),
         pointer = method["skip_binder"],
         true <-
           CallModels.expand(pointer["generics"], refs) ==
             Map.put(arguments([variable()]), "regions", [%{"Var" => %{"Bound" => [0, 0]}}]),
         function when not is_nil(function) <-
           Enum.find(translated["fun_decls"], &(&1 && &1["def_id"] == pointer["id"])),
         true <- function["body"] == "Opaque",
         true <-
           function["item_meta"]["name"] == expected_name ++ [%{"Builtin" => ["DropGlue", 0]}],
         true <- empty_parameters?(Map.put(function["generics"], "outlives", []), 1, 1),
         true <- valid_outlives?(function["generics"]["outlives"], refs),
         %{"abi" => "Rust", "is_unsafe" => true, "is_variadic" => false} = sig <-
           function["signature"],
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Ref" => [%{"Var" => %{"Free" => 0}}, self, "Mut"]}
           ],
         true <- unit?(CallModels.expand(sig["output"], refs)),
         %{"TraitImpl" => source} <- function["src"],
         true <- source["item_id"] == 0 and source["reuses_default"] == false,
         true <-
           CallModels.expand(source["impl_ref"], refs) == %{
             "id" => impl["def_id"],
             "generics" => arguments([variable()])
           },
         true <-
           CallModels.expand(source["trait_ref"], refs) == %{
             "id" => trait,
             "generics" => arguments([self])
           } do
      true
    else
      _ -> false
    end
  end

  defp valid_outlives?(outlives, refs),
    do:
      CallModels.expand(outlives, refs) == [
        %{
          "regions" => [],
          "outlives" => [],
          "skip_binder" => [%{"Lub" => variable()}, %{"Var" => %{"Free" => 0}}]
        }
      ]

  defp destruct?(id, translated, refs),
    do: Lynx.Rust.DropModels.destruct_trait?(id, translated, refs)

  # The specialized owning model closes a canonical standard File payload.
  # File/OS correspondence is explicit; arbitrary payload destructors are not inferred.
  defp file_payload?(payload, translated, refs) do
    with true <- get_in(translated, ["options", "owned_drops"]) == true,
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <-
           CallModels.expand(payload, refs),
         true <- args == arguments([]),
         %{"def_id" => ^id, "needs_drop" => true} <- Lynx.Rust.FileModels.declaration(translated) do
      true
    else
      _ -> false
    end
  end

  # Fields alone cannot establish the absence of a user Drop implementation.
  # Missing or unknown compiler evidence is deliberately not interpreted as false.
  def destructor_free?(type, translated, refs) do
    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} ->
        args == arguments([]) and
          Enum.any?(translated["type_decls"], fn
            %{
              "def_id" => ^id,
              "needs_drop" => false,
              "kind" => %{"Struct" => _},
              "generics" => params
            } ->
              params == %{
                "regions" => [],
                "types" => [],
                "const_generics" => [],
                "trait_clauses" => [],
                "trait_type_constraints" => [],
                "outlives" => []
              }

            _ ->
              false
          end)

      other ->
        scalar?(other)
    end
  end

  defp scalar?(%{"Scalar" => "Bool"}), do: true

  defp scalar?(%{"Scalar" => %{"Integer" => %{"Unsigned" => width}}})
       when width in ~w(U8 U16 U32 U64 U128 Usize), do: true

  defp scalar?(_), do: false

  defp parameters?(params),
    do:
      empty_parameters?(Map.put(params, "trait_clauses", []), 0, 1) and
        length(params["trait_clauses"]) == 1

  defp empty_parameters?(
         %{
           "regions" => regions,
           "types" => types,
           "const_generics" => [],
           "outlives" => [],
           "trait_clauses" => [],
           "trait_type_constraints" => []
         },
         r,
         t
       ),
       do:
         length(regions) == r and
           Enum.all?(Enum.with_index(regions), fn {p, i} -> p["index"] == i end) and
           length(types) == t and
           Enum.all?(Enum.with_index(types), fn {p, i} -> p["index"] == i end)

  defp empty_parameters?(_, _, _), do: false
  defp unit?(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}), do: args == arguments([])
  defp unit?(_), do: false
  defp variable, do: %{"TypeVar" => %{"Free" => 0}}

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp expand_trait(%{"Value" => [_, value]}, _), do: value
  defp expand_trait(%{"Deduplicated" => id}, refs), do: Map.fetch!(refs, id)
  defp expand_trait(value, _), do: value

  defp collect_refs(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = value]}, refs) do
    case Map.fetch(refs, id) do
      {:ok, existing} when existing != value ->
        raise ArgumentError, "inconsistent native drop trait-reference identity"

      _ ->
        Enum.reduce(Map.values(value), Map.put(refs, id, value), &collect_refs/2)
    end
  end

  defp collect_refs(map, refs) when is_map(map),
    do: Enum.reduce(Map.values(map), refs, &collect_refs/2)

  defp collect_refs(list, refs) when is_list(list), do: Enum.reduce(list, refs, &collect_refs/2)
  defp collect_refs(_, refs), do: refs
end
