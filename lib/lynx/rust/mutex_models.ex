defmodule Lynx.Rust.MutexModels do
  @moduledoc false
  alias Lynx.Rust.CallModels
  @path ~w(std sync poison mutex Mutex)

  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params,
           "item_meta" => %{"name" => name}
         } <- function,
         true <- parameters?(params),
         [
           %{"Ident" => ["std", 0]},
           %{"Ident" => ["sync", 0]},
           %{"Ident" => ["poison", 0]},
           %{"Ident" => ["mutex", 0]},
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
         ] <- name,
         true <- parameters?(parent_params),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <-
           CallModels.expand(parent, refs),
         true <- args == arguments([%{"TypeVar" => %{"Bound" => [0, 0]}}]),
         type when not is_nil(type) <-
           Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)),
         true <- type?(type),
         true <- CallModels.expand(sig["inputs"], refs) == [variable()],
         true <-
           CallModels.expand(sig["output"], refs) == %{
             "Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments([variable()])}
           } do
      %{
        rust_name: "std::sync::poison::mutex::{std::sync::poison::mutex::Mutex<@T>}::new",
        lean: "Lynx.NativeMutex.new",
        builtin: false,
        can_fail: true,
        native_cutoff_only: true,
        lift: true,
        native_mutex_type: id,
        native_constructor: true,
        native_transfer: true,
        label:
          "Logical Mutex::new model: atomic logical identity allocation, fresh shared identity, exact typed payload, unlocked and unpoisoned; std implementation and physical initialization/allocation unverified; guard unwind requires compiler-scoped captured cleanup; custom destructors and general unwind cleanup unsupported"
      }
    else
      _ -> nil
    end
  end

  def type?(%{"kind" => "Opaque", "item_meta" => %{"name" => name}, "generics" => params}),
    do: name == Enum.map(@path, &%{"Ident" => [&1, 0]}) and parameters?(params)

  def type?(_), do: false

  def type_models(calls, prefix) do
    if Enum.any?(calls, fn {_id, model} -> Map.has_key?(model, :native_mutex_type) end) do
      [
        %{
          rust: Enum.join(@path, "::"),
          lean: "Lynx.NativeMutex",
          import: (prefix |> String.split(".") |> hd()) <> ".NativeRuntime",
          label: "Typed movable native mutex identities; payload stored in the shared Lynx heap"
        }
      ]
    else
      []
    end
  end

  defp parameters?(%{
         "regions" => [],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "trait_type_constraints" => [],
         "outlives" => []
       }),
       do: true

  defp parameters?(_), do: false

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp variable, do: %{"TypeVar" => %{"Free" => 0}}
end
