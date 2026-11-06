defmodule Lynx.Rust.ResourceDrops do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, FormatModels, ResourceAudit, ResourceModels}

  def call?(args, t, refs, traits) do
    with %{
           "types" => [annotation],
           "regions" => [],
           "const_generics" => [],
           "trait_refs" => [dict]
         } <- args,
         %{"Adt" => %{"id" => arc, "builtin" => nil, "generics" => type_args}} = self <-
           CallModels.expand(annotation, refs),
         true <- ResourceModels.type?(find(t["type_decls"], arc)),
         %{"types" => [payload], "regions" => [], "const_generics" => [], "trait_refs" => []} <-
           type_args,
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => actual}},
           "trait_decl_ref" => decl
         } <- ResourceModels.dictionary(dict, traits),
         %{"types" => [_], "regions" => [], "const_generics" => [], "trait_refs" => [resource]} <-
           actual,
         true <- CallModels.expand(actual["types"], refs) == [payload],
         true <- DropModels.destruct_trait?(decl["id"], t, refs),
         true <- CallModels.expand(decl["generics"], refs) == ResourceModels.args([self]),
         {:ok, resource_trait, _} <-
           implementation(find(t["trait_impls"], impl_id), arc, decl["id"], t, refs, traits),
         true <- ResourceAudit.payload?(payload, resource, resource_trait, t, refs, traits) do
      true
    else
      _ -> false
    end
  end

  def site(drop, t, refs) do
    traits = ResourceModels.trait_references(t)

    with %{
           "kind" => "Precise",
           "place" => %{"ty" => annotation},
           "fn_ptr" => %{"kind" => %{"Fun" => fid}, "generics" => args}
         } <- drop,
         %{"Adt" => %{"id" => arc, "builtin" => nil, "generics" => type_args}} <-
           CallModels.expand(annotation, refs),
         true <- ResourceModels.type?(find(t["type_decls"], arc)),
         %{"types" => [payload], "regions" => [], "const_generics" => [], "trait_refs" => []} <-
           type_args,
         %{
           "types" => [_],
           "regions" => [%{"Body" => n}],
           "const_generics" => [],
           "trait_refs" => [resource]
         } <- args,
         true <- is_integer(n) and CallModels.expand(args["types"], refs) == [payload],
         function when not is_nil(function) <- find(t["fun_decls"], fid),
         %{"TraitImpl" => source} <- function["src"],
         impl_id = source["impl_ref"]["id"],
         trait = source["trait_ref"]["id"],
         true <- DropModels.destruct_trait?(trait, t, refs),
         {:ok, resource_trait, ^fid} <-
           implementation(find(t["trait_impls"], impl_id), arc, trait, t, refs, traits),
         true <- ResourceAudit.payload?(payload, resource, resource_trait, t, refs, traits) do
      {:ok,
       %{
         native_kind: :resource,
         function: fid,
         impl: impl_id,
         trait: trait,
         payload: hd(args["types"]),
         self: annotation,
         impl_arguments: ResourceModels.args(args["types"], [resource])
       }}
    else
      _ -> {:error, "unsupported resource destructor, payload or Resource callbacks"}
    end
  end

  defp implementation(nil, _, _, _, _, _), do: nil

  defp implementation(impl, arc, trait, t, refs, traits) do
    self = %{
      "Adt" => %{"id" => arc, "builtin" => nil, "generics" => ResourceModels.args([variable()])}
    }

    name =
      path(~w(rustler resource arc ResourceArc)) ++ [%{"Impl" => %{"Trait" => impl["def_id"]}}]

    with %{
           "src" => "Destruct",
           "is_negative" => false,
           "is_unsafe" => false,
           "types" => [],
           "consts" => [],
           "implied_trait_refs" => [],
           "methods" => [method]
         } <- impl,
         true <- impl["item_meta"]["name"] == name,
         params = CallModels.expand(impl["generics"], refs),
         [clause] <- params["trait_clauses"],
         resource_trait = clause["trait_"]["skip_binder"]["id"],
         true <-
           Enum.any?(
             t["trait_decls"],
             &(&1 && &1["def_id"] == resource_trait &&
                 &1["item_meta"]["name"] == path(~w(rustler resource traits Resource)))
           ),
         true <-
           ResourceModels.params?(params, 0, [clause]) and
             ResourceModels.resource_clause?(clause, resource_trait, refs),
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait,
             "generics" => ResourceModels.args([self])
           },
         f when not is_nil(f) <- find(t["fun_decls"], method["skip_binder"]["id"]),
         true <-
           f["body"] == "Opaque" and
             f["item_meta"]["name"] == name ++ [%{"Builtin" => ["DropGlue", 0]}],
         fp = CallModels.expand(f["generics"], refs),
         [fc] <- fp["trait_clauses"],
         true <-
           ResourceModels.params?(fp, 1, [fc], [bound()]) and
             ResourceModels.resource_clause?(fc, resource_trait, refs),
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
             traits: traits
           }) do
      {:ok, resource_trait, f["def_id"]}
    else
      _ -> nil
    end
  end

  defp variable, do: %{"TypeVar" => %{"Free" => 0}}

  defp bound,
    do: %{
      "regions" => [],
      "outlives" => [],
      "skip_binder" => [%{"Lub" => variable()}, %{"Var" => %{"Free" => 0}}]
    }

  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})
  defp find(values, id), do: Enum.find(values, &(&1 && &1["def_id"] == id))
end
