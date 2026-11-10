defmodule Lynx.Rust.GuardModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LockModels}

  # These are borrowed views, not acquisitions or releases. Aeneas's backward
  # function reconstructs the guard after a mutable borrow ends.
  def resolve(function, translated, refs) do
    function = CallModels.expand(function, refs)

    with %{
           "body" => "Opaque",
           "src" => %{"TraitImpl" => source},
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "generics" => params
         } <- function,
         %{"id" => impl_id} <- source["impl_ref"],
         %{"id" => trait_id} = trait_ref <- source["trait_ref"],
         true <- source["item_id"] == 0 and source["reuses_default"] == false,
         impl when not is_nil(impl) <- find(translated["trait_impls"], impl_id),
         trait when not is_nil(trait) <- find(translated["trait_decls"], trait_id),
         [%{"Ident" => [method, 0]}] <- Enum.drop(function["item_meta"]["name"], 5),
         true <- method in ~w(deref deref_mut),
         trait_name = if(method == "deref", do: "Deref", else: "DerefMut"),
         true <- trait["item_meta"]["name"] == path(~w(core ops deref) ++ [trait_name]),
         true <- trait["is_unsafe"] == false and trait["src"] == "Normal",
         [%{"Ref" => [_, %{"Adt" => %{"id" => guard_id}}, _]}] <- sig["inputs"],
         guard when not is_nil(guard) <- find(translated["type_decls"], guard_id),
         kind when not is_nil(kind) <- LockModels.guard_kind(guard, refs),
         true <- method != "deref_mut" or kind != :rw_read,
         self = adt(guard["def_id"]),
         expected_trait = %{"id" => trait_id, "generics" => arguments([self, variable()])},
         true <- trait_ref == expected_trait,
         true <-
           source["impl_ref"] == %{
             "id" => impl_id,
             "generics" => arguments([variable()], [region(0)])
           },
         true <- parameters?(params, 2, bounds()),
         name = Enum.take(LockModels.guard_path(kind), 4) ++ [%{"Impl" => %{"Trait" => impl_id}}],
         true <- function["item_meta"]["name"] == name ++ path([method]),
         impl = CallModels.expand(impl, refs),
         true <- impl["item_meta"]["name"] == name and impl["src"] == "Normal",
         true <- impl["is_unsafe"] == false and impl["is_negative"] == false,
         true <-
           impl["consts"] == [] and impl["types"] == if(method == "deref", do: [nil], else: []),
         true <- impl["impl_trait"] == expected_trait,
         true <- parent_view?(impl, method, translated, refs, self),
         true <- parameters?(impl["generics"], 1, [bound(%{"Lub" => variable()}, region(0))]),
         [entry] <- impl["methods"],
         true <- entry["kind"] == %{"TraitMethod" => [trait_id, 0]},
         true <- empty_method?(entry["params"]),
         true <-
           entry["skip_binder"] == %{
             "id" => function["def_id"],
             "generics" => arguments([variable()], [region(0), %{"Var" => %{"Bound" => [0, 0]}}])
           },
         mutability = if(method == "deref", do: "Shared", else: "Mut"),
         true <- sig["inputs"] == [%{"Ref" => [region(1), self, mutability]}],
         true <- sig["output"] == %{"Ref" => [region(1), variable(), mutability]} do
      family = if kind == :mutex, do: "mutex", else: "rwlock"

      %{
        rust_name:
          "std::sync::poison::#{family}::{core::ops::deref::#{trait_name}<std::sync::poison::#{family}::#{LockModels.guard_name(kind)}<'0, @T>, @T>}::#{method}",
        lean: "Lynx.#{LockModels.guard_module(kind)}.#{method}",
        native_guard_kind: kind,
        builtin: false,
        can_fail: false,
        lift: method == "deref_mut",
        native_guard_type: guard["def_id"],
        label:
          "Borrowed #{LockModels.guard_name(kind)} payload view#{if method == "deref_mut", do: " with mutable-borrow reconstruction", else: ""}; ownership and release remain separately audited; Rust std unsafe pointer dereference and FFI correctness unverified"
      }
    else
      _ -> nil
    end
  end

  defp parent_view?(impl, "deref", _, _, _), do: impl["implied_trait_refs"] == []

  defp parent_view?(impl, "deref_mut", translated, refs, self) do
    with [%{"regions" => [], "outlives" => [], "skip_binder" => parent}] <-
           impl["implied_trait_refs"],
         %{
           "kind" => %{"TraitImpl" => %{"id" => id, "generics" => args}},
           "trait_decl_ref" => decl
         } <- parent,
         true <- args == arguments([variable()], ["Erased"]),
         true <- decl["generics"] == arguments([self, variable()]),
         parent_impl when not is_nil(parent_impl) <- find(translated["trait_impls"], id),
         [method] <- parent_impl["methods"],
         function when not is_nil(function) <-
           find(translated["fun_decls"], method["skip_binder"]["id"]),
         %{"Ident" => ["deref", 0]} <- List.last(function["item_meta"]["name"]),
         %{lean: lean} <- resolve(function, translated, refs),
         true <- lean in ["Lynx.NativeGuard.deref", "Lynx.NativeRwWriteGuard.deref"],
         true <- CallModels.expand(parent_impl["impl_trait"], refs) == decl do
      true
    else
      _ -> false
    end
  end

  defp parameters?(
         %{
           "regions" => regions,
           "types" => [%{"index" => 0}],
           "const_generics" => [],
           "trait_clauses" => [],
           "trait_type_constraints" => [],
           "outlives" => outlives
         },
         count,
         expected
       ),
       do:
         Enum.map(regions, & &1["index"]) == Enum.to_list(0..(count - 1)) and outlives == expected

  defp parameters?(_, _, _), do: false

  defp empty_method?(%{
         "regions" => [%{"index" => 0}],
         "types" => [],
         "const_generics" => [],
         "trait_clauses" => [],
         "trait_type_constraints" => [],
         "outlives" => []
       }),
       do: true

  defp empty_method?(_), do: false

  defp bounds,
    do: [
      bound(%{"Lub" => variable()}, region(0)),
      bound(region(0), region(1)),
      bound(%{"Lub" => variable()}, region(1))
    ]

  defp bound(left, right),
    do: %{"regions" => [], "outlives" => [], "skip_binder" => [left, right]}

  defp adt(id),
    do: %{
      "Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments([variable()], [region(0)])}
    }

  defp arguments(types, regions \\ []),
    do: %{"regions" => regions, "types" => types, "const_generics" => [], "trait_refs" => []}

  defp variable, do: %{"TypeVar" => %{"Free" => 0}}
  defp region(i), do: %{"Var" => %{"Free" => i}}
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp find(items, id), do: Enum.find(items, &(&1 && &1["def_id"] == id))
end
