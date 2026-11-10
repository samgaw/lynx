defmodule Lynx.Rust.GuardDrops do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, LockModels}

  # Releasing a guard borrows its payload; it never destroys that payload.
  # This validates the compiler's concrete Destruct dictionary, not merely a
  # generic call to mem::drop or a function with the same short name.
  def call?(generics, translated, refs, trait_refs) do
    with %{
           "types" => [type],
           "regions" => [],
           "const_generics" => [],
           "trait_refs" => [%{"regions" => [], "outlives" => [], "skip_binder" => dictionary}]
         } <- generics,
         %{"Adt" => %{"id" => guard, "builtin" => nil, "generics" => args}} = self <-
           CallModels.expand(type, refs),
         true <- LockModels.guard?(find(translated["type_decls"], guard), refs),
         %{
           "types" => [payload],
           "regions" => [%{"Body" => region}],
           "const_generics" => [],
           "trait_refs" => []
         } <- args,
         true <- is_integer(region),
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => actual}},
           "trait_decl_ref" => decl
         } <- expand_trait(dictionary, trait_refs),
         true <- CallModels.expand(actual, refs) == arguments([payload], [%{"Body" => region}]),
         true <- DropModels.destruct_trait?(decl["id"], translated, refs),
         true <- CallModels.expand(decl["generics"], refs) == arguments([self]),
         true <-
           implementation?(
             find(translated["trait_impls"], impl_id),
             guard,
             decl["id"],
             translated,
             refs
           ) do
      true
    else
      _ -> false
    end
  end

  def site(drop, translated, refs) do
    with %{
           "place" => %{"ty" => annotation},
           "kind" => "Precise",
           "fn_ptr" => %{"kind" => %{"Fun" => id}, "generics" => call_args}
         } <- drop,
         %{
           "Adt" => %{
             "id" => guard,
             "generics" => %{
               "regions" => [%{"Body" => lifetime}],
               "types" => [payload],
               "const_generics" => [],
               "trait_refs" => []
             }
           }
         } <- CallModels.expand(annotation, refs),
         true <- is_integer(lifetime),
         true <- LockModels.guard?(find(translated["type_decls"], guard), refs),
         %{
           "regions" => [%{"Body" => first}, %{"Body" => second}],
           "types" => [_],
           "const_generics" => [],
           "trait_refs" => []
         } <- call_args,
         true <- is_integer(first) and is_integer(second),
         true <- CallModels.expand(call_args["types"], refs) == [payload],
         function when not is_nil(function) <- find(translated["fun_decls"], id),
         %{"TraitImpl" => source} <- function["src"],
         impl when not is_nil(impl) <- find(translated["trait_impls"], source["impl_ref"]["id"]),
         trait = source["trait_ref"]["id"],
         true <- DropModels.destruct_trait?(trait, translated, refs),
         true <- implementation?(impl, guard, trait, translated, refs),
         [method] <- impl["methods"],
         true <- method["skip_binder"]["id"] == id do
      {:ok,
       %{
         native_kind: :guard,
         function: id,
         impl: impl["def_id"],
         trait: trait,
         payload: hd(call_args["types"]),
         self: annotation,
         impl_arguments: arguments([hd(call_args["types"])], [%{"Body" => lifetime}])
       }}
    else
      _ -> {:error, "unsupported guard drop site or inconsistent compiler destructor"}
    end
  end

  defp implementation?(nil, _, _, _, _), do: false

  defp implementation?(impl, guard, trait, translated, refs) do
    impl = CallModels.expand(impl, refs)

    self = %{
      "Adt" => %{
        "id" => guard,
        "builtin" => nil,
        "generics" => arguments([variable()], [region(0)])
      }
    }

    name =
      LockModels.guard_path(LockModels.guard_kind(find(translated["type_decls"], guard), refs)) ++
        [%{"Impl" => %{"Trait" => impl["def_id"]}}]

    with %{
           "src" => "Destruct",
           "is_negative" => false,
           "is_unsafe" => false,
           "consts" => [],
           "types" => [],
           "implied_trait_refs" => [],
           "methods" => [method]
         } <- impl,
         true <- impl["item_meta"]["name"] == name,
         true <- parameters?(impl["generics"], 1, 1, [bound(%{"Lub" => variable()}, region(0))]),
         expected_trait = %{"id" => trait, "generics" => arguments([self])},
         true <- impl["impl_trait"] == expected_trait,
         true <- method["kind"] == %{"TraitMethod" => [trait, 0]},
         true <- parameters?(method["params"], 1, 0, []),
         pointer = method["skip_binder"],
         true <-
           pointer["generics"] ==
             arguments([variable()], [region(0), %{"Var" => %{"Bound" => [0, 0]}}]),
         function when not is_nil(function) <- find(translated["fun_decls"], pointer["id"]),
         function = CallModels.expand(function, refs),
         true <- function["body"] == "Opaque",
         true <- function["item_meta"]["name"] == name ++ [%{"Builtin" => ["DropGlue", 0]}],
         true <-
           parameters?(function["generics"], 2, 1, [
             bound(%{"Lub" => variable()}, region(0)),
             bound(region(0), region(1)),
             bound(%{"Lub" => variable()}, region(1))
           ]),
         %{"abi" => "Rust", "is_unsafe" => true, "is_variadic" => false} = signature <-
           function["signature"],
         true <- signature["inputs"] == [%{"Ref" => [region(1), self, "Mut"]}],
         %{"Adt" => %{"builtin" => "Tuple", "generics" => unit}} <- signature["output"],
         true <- unit == arguments([]),
         true <-
           function["src"] == %{
             "TraitImpl" => %{
               "item_id" => 0,
               "reuses_default" => false,
               "impl_ref" => %{
                 "id" => impl["def_id"],
                 "generics" => arguments([variable()], [region(0)])
               },
               "trait_ref" => expected_trait
             }
           } do
      true
    else
      _ -> false
    end
  end

  defp parameters?(
         %{
           "regions" => regions,
           "types" => types,
           "const_generics" => [],
           "trait_clauses" => [],
           "trait_type_constraints" => [],
           "outlives" => outlives
         },
         nr,
         nt,
         expected
       ),
       do:
         Enum.map(regions, & &1["index"]) == indices(nr) and
           Enum.map(types, & &1["index"]) == indices(nt) and outlives == expected

  defp parameters?(_, _, _, _), do: false
  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))

  defp arguments(types, regions \\ []),
    do: %{"types" => types, "regions" => regions, "const_generics" => [], "trait_refs" => []}

  defp variable, do: %{"TypeVar" => %{"Free" => 0}}
  defp region(i), do: %{"Var" => %{"Free" => i}}

  defp bound(left, right),
    do: %{"regions" => [], "outlives" => [], "skip_binder" => [left, right]}

  defp find(items, id), do: Enum.find(items, &(&1 && &1["def_id"] == id))
  defp expand_trait(%{"Value" => [_, value]}, _), do: value
  defp expand_trait(%{"Deduplicated" => id}, refs), do: Map.get(refs, id)
  defp expand_trait(value, _), do: value
end
