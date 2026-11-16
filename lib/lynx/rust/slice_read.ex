defmodule Lynx.Rust.SliceRead do
  @moduledoc false
  alias Lynx.Rust.{CallModels, ResourceModels}

  def selected?(
        %{
          "body" => %{"Structured" => _},
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["alloc", 0]},
              %{"Ident" => ["io", 0]},
              %{"Ident" => ["impls", 0]},
              %{"Impl" => %{"Trait" => _}},
              %{"Ident" => ["read_exact", 0]}
            ]
          }
        } = function,
        translated
      ) do
    refs = Lynx.Rust.LLBC.type_references!(translated)
    function = CallModels.expand(function, refs)

    with %{
           "src" => %{
             "TraitImpl" => %{
               "impl_ref" => %{"id" => impl_id},
               "trait_ref" => %{"id" => trait},
               "item_id" => 5,
               "reuses_default" => false
             }
           },
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params,
           "item_meta" => %{"name" => name}
         } <- function,
         true <-
           name ==
             path(~w(alloc io impls)) ++
               [%{"Impl" => %{"Trait" => impl_id}}, %{"Ident" => ["read_exact", 0]}],
         true <- empty?(params, [0, 1, 2]),
         true <-
           params["outlives"] == [
             %{
               "regions" => [],
               "outlives" => [],
               "skip_binder" => [%{"Var" => %{"Free" => 0}}, %{"Var" => %{"Free" => 1}}]
             }
           ],
         [declaration] <- Enum.filter(translated["trait_decls"], &(&1 && &1["def_id"] == trait)),
         true <- declaration["item_meta"]["name"] == path(~w(alloc io read Read)),
         [impl] <- Enum.filter(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         impl = CallModels.expand(impl, refs),
         true <- impl["src"] == "Normal" and !impl["is_unsafe"] and !impl["is_negative"],
         true <- empty?(impl["generics"], [0]) and impl["generics"]["outlives"] == [],
         self = reference(0, slice(), "Shared"),
         true <- impl["impl_trait"] == %{"id" => trait, "generics" => ResourceModels.args([self])},
         [%{"skip_binder" => %{"id" => id}}] <-
           Enum.filter(impl["methods"], &(&1 && &1["kind"] == %{"TraitMethod" => [trait, 5]})),
         true <- id == function["def_id"],
         true <- sig["inputs"] == [reference(1, self, "Mut"), reference(2, slice(), "Mut")],
         true <- result?(sig["output"], translated, refs) do
      true
    else
      _ -> false
    end
  end

  def selected?(_, _), do: false

  defp result?(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}}, translated, refs) do
    with [unit, error] <- args["types"],
         true <-
           unit == %{
             "Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => ResourceModels.args([])}
           },
         true <- args == ResourceModels.args([unit, error]),
         true <- Lynx.Rust.LLBC.result_type?(id, %{translated: translated, references: refs}),
         %{"Adt" => %{"id" => error_id, "builtin" => nil, "generics" => empty}} <- error,
         true <- empty == ResourceModels.args([]) do
      Lynx.Rust.FileModels.error_type?(translated, error_id)
    else
      _ -> false
    end
  end

  defp result?(_, _, _), do: false

  defp empty?(params, regions) do
    Enum.map(params["regions"], & &1["index"]) == regions and
      Enum.all?(
        ~w(types const_generics trait_clauses trait_type_constraints),
        &(params[&1] == [])
      )
  end

  defp slice, do: %{"Slice" => [%{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}, nil]}

  defp reference(region, type, kind),
    do: %{"Ref" => [%{"Var" => %{"Free" => region}}, type, kind]}

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
