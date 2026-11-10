defmodule Lynx.Rust.BoxModels do
  @moduledoc false
  alias Lynx.Rust.CallModels
  @args %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}
  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => params,
           "signature" =>
             %{"is_unsafe" => false, "abi" => "Rust", "is_variadic" => false} = signature,
           "item_meta" => %{
             "diagnostic_item" => "box_new",
             "has_errors" => false,
             "name" => [
               %{"Ident" => ["alloc", 0]},
               %{"Ident" => ["boxed", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent_params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => ["new", 0]}
             ]
           }
         } <- function,
         true <- parameters?(params) && parameters?(parent_params),
         variable = %{"TypeVar" => %{"Free" => 0}},
         [^variable] <- CallModels.expand(signature["inputs"], refs),
         %{"Adt" => %{"id" => id, "builtin" => "Box", "generics" => args}} = output <-
           CallModels.expand(signature["output"], refs),
         true <- args == %{@args | "types" => [variable]},
         [box] <- Enum.filter(translated["type_decls"], &(&1 && &1["def_id"] == id)),
         true <-
           box["kind"] == "Opaque" && box["item_meta"]["has_errors"] == false &&
             parameters?(box["generics"]) &&
             box["item_meta"]["name"] == Enum.map(~w(alloc boxed Box), &%{"Ident" => [&1, 0]}),
         true <- bound_to_free(CallModels.expand(parent, refs)) == output do
      %{
        rust_name: "alloc::boxed::Box<@T>::new",
        lean: "Aeneas.Std.alloc.boxed.Box.new",
        builtin: true,
        can_fail: false,
        lift: false,
        label:
          "Aeneas logical heap Box::new preserves its owned value; allocation success, native allocation failure/abort and heap correspondence remain unverified assumptions"
      }
    else
      _ -> nil
    end
  end

  defp parameters?(%{"types" => [%{"index" => 0}]} = params),
    do: Enum.all?(Map.delete(params, "types"), fn {_, value} -> value == [] end)

  defp parameters?(_), do: false
  defp bound_to_free(%{"TypeVar" => %{"Bound" => [0, 0]}}), do: %{"TypeVar" => %{"Free" => 0}}

  defp bound_to_free(map) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, bound_to_free(v)} end)

  defp bound_to_free(list) when is_list(list), do: Enum.map(list, &bound_to_free/1)
  defp bound_to_free(value), do: value
end
