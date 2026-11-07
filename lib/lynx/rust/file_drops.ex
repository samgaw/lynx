defmodule Lynx.Rust.FileDrops do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, FileModels, FormatModels, NativeDrops, ResourceModels}

  def resolve(function, t, refs) do
    with true <- NativeDrops.consuming_function?(function, t, refs),
         %{"def_id" => id, "needs_drop" => true} <- FileModels.declaration(t) do
      base =
        NativeDrops.resolve(function, t, refs) ||
          %{
            rust_name: "core::mem::drop",
            lean:
              if(get_in(t, ["options", "owned_drops"]) == true,
                do: "Lynx.NativeOwnedDrop.drop",
                else: "Lynx.NativeDrop.drop"
              ),
            builtin: false,
            can_fail: true,
            lift: true,
            native_cutoff_only: true,
            native_dispose: true,
            native_codec_drop: true
          }

      Map.merge(base, %{
        native_file_drop: true,
        native_file_types: {id, nil},
        label:
          Map.get(base, :label, "") <>
            " Standard File destruction model: consuming a registered file retires its Rust capability while retaining visible/durable disk state; ignored native close errors do not restore ownership or acknowledge durability; admitted close persistence is explicit; physical descriptor reclamation, debug-validity checks, std, allocation, OS and FFI correspondence unverified; nested File ownership and panic cleanup unsupported"
      })
    else
      _ -> nil
    end
  end

  def call?(args, t, refs, traits) do
    with %{
           "types" => [annotation],
           "regions" => [],
           "const_generics" => [],
           "trait_refs" => [dict]
         } <- args,
         %{"Adt" => %{"id" => file, "builtin" => nil, "generics" => actual}} = self <-
           CallModels.expand(annotation, refs),
         true <- actual == ResourceModels.args([]) and FileModels.file_type?(t, file),
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl, "generics" => impl_args}},
           "trait_decl_ref" => decl
         } <- ResourceModels.dictionary(dict, traits),
         true <- CallModels.expand(impl_args, refs) == ResourceModels.args([]),
         true <- DropModels.destruct_trait?(decl["id"], t, refs),
         true <- CallModels.expand(decl["generics"], refs) == ResourceModels.args([self]),
         {:ok, _} <- implementation(find(t["trait_impls"], impl), file, decl["id"], t, refs) do
      true
    else
      _ -> false
    end
  end

  def site(drop, t, refs) do
    with %{
           "kind" => "Precise",
           "place" => %{"ty" => annotation},
           "fn_ptr" => %{"kind" => %{"Fun" => fid}, "generics" => args}
         } <- drop,
         %{"Adt" => %{"id" => file, "builtin" => nil, "generics" => actual}} <-
           CallModels.expand(annotation, refs),
         true <- actual == ResourceModels.args([]) and FileModels.file_type?(t, file),
         true <-
           CallModels.expand(args, refs) ==
             Map.put(ResourceModels.args([]), "regions", [%{"Body" => body_region(args)}]),
         region when is_integer(region) <- body_region(args),
         function when not is_nil(function) <- find(t["fun_decls"], fid),
         %{"TraitImpl" => source} <- function["src"],
         true <- DropModels.destruct_trait?(source["trait_ref"]["id"], t, refs),
         {:ok, ^fid} <-
           implementation(
             find(t["trait_impls"], source["impl_ref"]["id"]),
             file,
             source["trait_ref"]["id"],
             t,
             refs
           ) do
      {:ok,
       %{
         function: fid,
         native_kind: :file,
         impl: source["impl_ref"]["id"],
         trait: source["trait_ref"]["id"],
         payload: annotation,
         self: annotation,
         impl_arguments: ResourceModels.args([])
       }}
    else
      _ -> {:error, "unsupported File destructor or inconsistent compiler close identity"}
    end
  end

  defp implementation(impl, file, trait, t, refs) do
    self = %{"Adt" => %{"id" => file, "builtin" => nil, "generics" => ResourceModels.args([])}}

    with %{
           "src" => "Destruct",
           "is_negative" => false,
           "is_unsafe" => false,
           "types" => [],
           "consts" => [],
           "implied_trait_refs" => [],
           "methods" => [method]
         } <- impl,
         true <- FileModels.file_type?(t, file),
         %{"needs_drop" => true} <- FileModels.declaration(t),
         true <- plain?(impl["generics"], 0),
         name = path(~w(std fs File)) ++ [%{"Impl" => %{"Trait" => impl["def_id"]}}],
         true <- impl["item_meta"]["name"] == name,
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait,
             "generics" => ResourceModels.args([self])
           },
         true <- method["kind"] == %{"TraitMethod" => [trait, 0]} and plain?(method["params"], 1),
         ptr = method["skip_binder"],
         true <-
           CallModels.expand(ptr["generics"], refs) ==
             Map.put(ResourceModels.args([]), "regions", [%{"Var" => %{"Bound" => [0, 0]}}]),
         f when not is_nil(f) <- find(t["fun_decls"], ptr["id"]),
         true <-
           f["body"] == "Opaque" and
             f["item_meta"]["name"] == name ++ [%{"Builtin" => ["DropGlue", 0]}],
         true <- plain?(f["generics"], 1),
         %{"abi" => "Rust", "is_unsafe" => true, "is_variadic" => false} = sig <- f["signature"],
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Ref" => [%{"Var" => %{"Free" => 0}}, self, "Mut"]}
           ],
         %{"Adt" => %{"builtin" => "Tuple", "generics" => unit}} <-
           CallModels.expand(sig["output"], refs),
         true <- unit == ResourceModels.args([]),
         true <-
           FormatModels.method_identity?(f, impl, trait, %{
             translated: t,
             refs: refs,
             traits: ResourceModels.trait_references(t)
           }) do
      {:ok, f["def_id"]}
    else
      _ -> nil
    end
  end

  defp plain?(p, regions),
    do:
      is_map(p) and p["types"] == [] and p["const_generics"] == [] and
        p["trait_clauses"] == [] and p["trait_type_constraints"] == [] and p["outlives"] == [] and
        is_list(p["regions"]) and length(p["regions"]) == regions and
        Enum.all?(Enum.with_index(p["regions"]), fn {region, index} ->
          region["index"] == index
        end)

  defp body_region(%{"regions" => [%{"Body" => region}]}), do: region
  defp body_region(_), do: nil
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp find(items, id), do: Enum.find(items, &(&1 && &1["def_id"] == id))
end
