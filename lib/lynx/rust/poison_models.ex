defmodule Lynx.Rust.PoisonModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LockModels}

  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => params,
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "item_meta" => %{"name" => name}
         } <- function,
         [
           a,
           b,
           c,
           %{
             "Impl" => %{
               "Ty" => %{
                 "kind" => "InherentImplBlock",
                 "params" => parent_params,
                 "skip_binder" => parent
               }
             }
           },
           %{"Ident" => ["into_inner", 0]}
         ] <- name,
         true <- [a, b, c] == path(~w(std sync poison)),
         true <- parameters?(params) and parameters?(parent_params),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <-
           CallModels.expand(parent, refs),
         true <- args == arguments([%{"TypeVar" => %{"Bound" => [0, 0]}}]),
         true <-
           LockModels.poison?(Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id))),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments([variable()])}}
           ],
         true <- CallModels.expand(sig["output"], refs) == variable() do
      guard = Enum.find(translated["type_decls"], &LockModels.guard?(&1, refs))

      %{
        rust_name: "std::sync::poison::{std::sync::poison::PoisonError<@T>}::into_inner",
        lean: "Lynx.NativePoisonError.into_inner",
        builtin: false,
        can_fail: false,
        lift: false,
        native_transfer: true,
        native_poison_type: id,
        label:
          "Consuming PoisonError::into_inner model: transfers the owned payload without clearing poison or acquiring/releasing a lock; Rust std and native layout unverified"
      }
      |> then(fn model ->
        if guard, do: Map.put(model, :native_guard_type, guard["def_id"]), else: model
      end)
    else
      _ -> nil
    end
  end

  defp parameters?(%{
         "regions" => [],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "outlives" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp parameters?(_), do: false

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp variable, do: %{"TypeVar" => %{"Free" => 0}}
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
