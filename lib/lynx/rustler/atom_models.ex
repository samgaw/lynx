defmodule Lynx.Rustler.AtomModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, ResourceModels}
  @empty %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  def resolve(
        %{"body" => "Opaque", "item_meta" => %{"has_errors" => false}} = function,
        translated,
        refs
      ) do
    ctx = %{translated: translated, refs: refs}

    cond do
      function["item_meta"]["name"] == path(~w(core cmp PartialEq ne)) ->
        default_ne(function, ctx)

      true ->
        atom_eq(function, ctx)
    end
  end

  def resolve(_, _, _), do: nil

  defp atom_eq(function, ctx) do
    with %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => impl_id, "generics" => @empty},
             "trait_ref" => %{"id" => trait, "generics" => trait_args},
             "item_id" => 0,
             "reuses_default" => false
           }
         } <- function["src"],
         true <-
           function["item_meta"]["name"] ==
             path(~w(rustler types atom)) ++
               [%{"Impl" => %{"Trait" => impl_id}}, %{"Ident" => ["eq", 0]}],
         %{"def_id" => atom, "kind" => "Opaque"} <- named_type(ctx, ~w(rustler types atom Atom)),
         self = adt(atom),
         true <- partial_eq?(trait, ctx, false),
         true <- expand(trait_args, ctx) == args([self, self]),
         true <- params?(function["generics"], 2, 0),
         true <- expand(function["signature"], ctx) == signature(self, self, &region/1),
         %{
           "src" => "Normal",
           "is_negative" => false,
           "is_unsafe" => false,
           "consts" => [],
           "types" => [],
           "implied_trait_refs" => [],
           "generics" => params,
           "impl_trait" => implemented,
           "methods" => [eq, _]
         } = impl <- find(ctx, "trait_impls", impl_id),
         true <- params?(params, 0, 0),
         true <-
           impl["item_meta"]["name"] ==
             path(~w(rustler types atom)) ++ [%{"Impl" => %{"Trait" => impl_id}}],
         true <- impl["item_meta"]["has_errors"] == false,
         true <- expand(implemented, ctx) == %{"id" => trait, "generics" => args([self, self])},
         %{
           "kind" => %{"TraitMethod" => [^trait, 0]},
           "params" => method_params,
           "skip_binder" => %{"id" => id, "generics" => method_args}
         } <- eq,
         true <- id == function["def_id"] and params?(method_params, 2, 0),
         true <- method_args == %{@empty | "regions" => [bound(0), bound(1)]} do
      %{
        rust_name:
          "rustler::types::atom::{core::cmp::PartialEq<rustler::types::atom::Atom, rustler::types::atom::Atom>}::eq",
        lean: "Lynx.Rustler.atomEq",
        builtin: false,
        can_fail: true,
        lift: false,
        atom_eq: true,
        atom_impl: impl_id,
        atom_trait: trait,
        label:
          "Rustler Atom equality model: exact interned atom identity represented by names; native word representation, atom interning and SDK/OTP implementation unverified"
      }
    else
      _ -> nil
    end
  end

  defp default_ne(function, ctx) do
    t = var(0)
    u = var(1)

    with %{
           "TraitDefault" => %{
             "trait_ref" => %{"id" => trait, "generics" => trait_args},
             "item_id" => 1
           }
         } <- function["src"],
         true <- partial_eq?(trait, ctx),
         true <- expand(trait_args, ctx) == args([t, u]),
         true <- expand(function["signature"], ctx) == signature(t, u, &region/1),
         params = expand(function["generics"], ctx),
         true <- params?(%{params | "trait_clauses" => [], "outlives" => []}, 2, 2),
         true <- params["outlives"] == [outlives(t, region(0)), outlives(u, region(1))],
         [
           %{
             "clause_id" => 0,
             "origin" => "TraitSelf",
             "trait_" => %{
               "regions" => [],
               "outlives" => [],
               "skip_binder" => %{"id" => ^trait, "generics" => clause_args}
             }
           }
         ] <- params["trait_clauses"],
         true <- clause_args == args([t, u]),
         trait_decl = find(ctx, "trait_decls", trait),
         [_, ne] = trait_decl["methods"],
         true <- standard_default?(ne["skip_binder"]["default"], function["def_id"], trait, ctx) do
      %{
        rust_name: "core::cmp::PartialEq::ne",
        lean: "Aeneas.Std.core.cmp.PartialEq.ne.trait_default",
        builtin: true,
        can_fail: true,
        lift: false,
        atom_ne: true,
        atom_trait: trait,
        label:
          "Existing Aeneas default PartialEq::ne model invokes the audited SDK Atom equality dictionary; other dictionaries rejected; Rust core implementation unverified"
      }
    else
      _ -> nil
    end
  end

  # A default method must not make an arbitrary foreign equality implementation
  # callable. Close its concrete dictionary over the separately validated SDK
  # method, and retain that method as an implementation-linking dependency.
  def dependencies!(id, actual, ctx) do
    with %{
           "regions" => [_, _],
           "types" => [left, right],
           "const_generics" => [],
           "trait_refs" => [dict]
         } <- actual,
         %{"def_id" => atom, "kind" => "Opaque"} <- named_type(ctx, ~w(rustler types atom Atom)),
         self = adt(atom),
         true <- expand(left, ctx) == self and expand(right, ctx) == self,
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => @empty}},
           "trait_decl_ref" => %{"id" => trait, "generics" => trait_args}
         } <- ResourceModels.dictionary(dict, ctx.traits),
         true <-
           trait == ctx.models[id].atom_trait and expand(trait_args, ctx) == args([self, self]),
         %{"methods" => [eq, ne]} <- find(ctx, "trait_impls", impl_id),
         %{"skip_binder" => %{"id" => method}} <- eq,
         %{atom_eq: true, atom_impl: ^impl_id, atom_trait: ^trait} <- ctx.models[method],
         %{
           "kind" => %{"TraitMethod" => [^trait, 1]},
           "params" => params,
           "skip_binder" => %{"id" => ^id, "generics" => reused}
         } <- ne,
         true <- params?(params, 2, 0),
         true <-
           reused["regions"] == [bound(0), bound(1)] and reused["const_generics"] == [] and
             expand(reused["types"], ctx) == [self, self],
         [again] <- reused["trait_refs"],
         true <-
           ResourceModels.dictionary(again, ctx.traits) ==
             ResourceModels.dictionary(dict, ctx.traits) do
      [method]
    else
      _ ->
        raise ArgumentError,
              "default PartialEq::ne requires the validated concrete Rustler Atom equality implementation"
    end
  end

  defp standard_default?(%{"id" => id, "generics" => actual}, id, trait, ctx) do
    with %{
           "regions" => [r0, r1],
           "types" => types,
           "const_generics" => [],
           "trait_refs" => [dict]
         } <- actual,
         true <- [r0, r1] == [bound(0), bound(1)] and expand(types, ctx) == [var(0), var(1)],
         %{"kind" => "SelfId", "trait_decl_ref" => %{"id" => ^trait, "generics" => declared}} <-
           ResourceModels.dictionary(dict, ResourceModels.trait_references(ctx.translated)),
         true <- expand(declared, ctx) == args([var(0), var(1)]),
         do: true,
         else: (_ -> false)
  end

  defp standard_default?(_, _, _, _), do: false

  defp partial_eq?(id, ctx, require_ne \\ true) do
    with %{
           "item_meta" => %{"name" => name, "has_errors" => false},
           "is_unsafe" => false,
           "consts" => [],
           "types" => [],
           "implied_clauses" => [],
           "generics" => params,
           "methods" => [eq, ne]
         } <- find(ctx, "trait_decls", id),
         true <- name == path(~w(core cmp PartialEq)) and params?(params, 0, 2) do
      Enum.all?([{eq, 0, "eq"}] ++ if(ne, do: [{ne, 1, "ne"}], else: []), fn {method, index, name} ->
        method["kind"] == %{"TraitMethod" => [id, index]} and params?(method["params"], 2, 0) and
          method["skip_binder"]["name"] == name and
          expand(method["skip_binder"]["signature"], ctx) == signature(var(0), var(1), &bound/1)
      end) and eq["skip_binder"]["default"] == nil and
        (is_map(ne["skip_binder"]["default"]) or (not require_ne and ne == nil))
    else
      _ -> false
    end
  end

  defp signature(left, right, region),
    do: %{
      "is_unsafe" => false,
      "is_variadic" => false,
      "abi" => "Rust",
      "inputs" => [
        %{"Ref" => [region.(0), left, "Shared"]},
        %{"Ref" => [region.(1), right, "Shared"]}
      ],
      "output" => %{"Scalar" => "Bool"}
    }

  defp params?(params, regions, types),
    do:
      is_map(params) and
        Enum.map(params["regions"], & &1["index"]) == indices(regions) and
        Enum.map(params["types"], & &1["index"]) == indices(types) and
        Enum.all?(
          ~w(const_generics trait_clauses outlives trait_type_constraints),
          &(params[&1] == [])
        )

  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))
  defp find(ctx, key, id), do: Enum.find(ctx.translated[key], &(&1 && &1["def_id"] == id))

  defp named_type(ctx, name),
    do: Enum.find(ctx.translated["type_decls"], &(&1 && &1["item_meta"]["name"] == path(name)))

  defp expand(value, ctx), do: CallModels.expand(value, ctx.refs)
  defp args(types), do: %{@empty | "types" => types}
  defp adt(id), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => @empty}}
  defp var(n), do: %{"TypeVar" => %{"Free" => n}}
  defp region(n), do: %{"Var" => %{"Free" => n}}
  defp bound(n), do: %{"Var" => %{"Bound" => [0, n]}}

  defp outlives(t, r),
    do: %{"regions" => [], "outlives" => [], "skip_binder" => [%{"Lub" => t}, r]}

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
