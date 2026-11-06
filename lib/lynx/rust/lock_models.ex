defmodule Lynx.Rust.LockModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, MutexModels}
  @base ~w(std sync poison mutex)

  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => params,
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "item_meta" => %{"name" => name}
         } <- function,
         [
           a,
           b,
           c,
           d,
           %{
             "Impl" => %{
               "Ty" => %{
                 "kind" => "InherentImplBlock",
                 "params" => parent_params,
                 "skip_binder" => parent
               }
             }
           },
           %{"Ident" => ["lock", 0]}
         ] <- name,
         true <- [a, b, c, d] == path(@base),
         true <- params?(parent_params, 0, []),
         true <- params?(CallModels.expand(params, refs), 1, [outlives()]),
         %{"Adt" => %{"id" => mutex, "builtin" => nil, "generics" => args}} <-
           CallModels.expand(parent, refs),
         true <- args == arguments([%{"TypeVar" => %{"Bound" => [0, 0]}}]),
         true <-
           Enum.any?(
             translated["type_decls"],
             &(&1 && &1["def_id"] == mutex && MutexModels.type?(&1))
           ),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Ref" => [region(), adt(mutex, [variable()]), "Shared"]}
           ],
         guard when not is_nil(guard) <- Enum.find(translated["type_decls"], &guard?(&1, refs)),
         poison when not is_nil(poison) <- Enum.find(translated["type_decls"], &poison?/1),
         %{"Adt" => %{"id" => result, "generics" => result_args, "builtin" => nil}} <-
           CallModels.expand(sig["output"], refs),
         true <- LLBC.result_type?(result, %{translated: translated, references: refs}),
         guard_type = adt(guard["def_id"], [variable()], [region()]),
         true <- result_args == arguments([guard_type, adt(poison["def_id"], [guard_type])]) do
      %{
        rust_name: "std::sync::poison::mutex::{std::sync::poison::mutex::Mutex<@T>}::lock",
        lean: "Lynx.NativeMutex.lock",
        builtin: false,
        can_fail: true,
        lift: true,
        native_mutex_type: mutex,
        native_guard_type: guard["def_id"],
        native_poison_type: poison["def_id"],
        native_codec_input: true,
        label:
          "Blocking Mutex::lock model: atomic shared-cell acquisition; poisoned acquisition returns an owned guard in PoisonError; recursive acquisition and malformed identities exhaust verification; logical execution contexts are local Lynx processes; native async/thread migration, Rust std and FFI implementation correctness unverified"
      }
    else
      _ -> nil
    end
  end

  def guard?(
        %{
          "src" => "Normal",
          "kind" => "Opaque",
          "generics" => params,
          "item_meta" => %{"name" => name}
        },
        refs
      ),
      do:
        name == path(@base ++ ["MutexGuard"]) and
          params?(CallModels.expand(params, refs), 1, [outlives(), outlives()])

  def guard?(_, _), do: false

  def poison?(%{
        "src" => "Normal",
        "kind" => "Opaque",
        "generics" => params,
        "item_meta" => %{"name" => name}
      }),
      do: name == path(~w(std sync poison PoisonError)) and params?(params, 0, [])

  def poison?(_), do: false

  def type_models(models, prefix) do
    module = (prefix |> String.split(".") |> hd()) <> ".NativeRuntime"

    for {key, rust, lean} <- [
          {:native_guard_type, "std::sync::poison::mutex::MutexGuard", "Lynx.NativeGuard"},
          {:native_poison_type, "std::sync::poison::PoisonError", "Lynx.NativePoisonError"}
        ],
        Enum.any?(models, fn {_, model} -> model[key] end),
        do: %{
          rust: rust,
          lean: lean,
          import: module,
          label:
            "Validated native guard/poisoned-acquisition representation; Rust std and native layout unverified"
        }
  end

  defp params?(
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
         length(regions) == count and
           Enum.all?(Enum.with_index(regions), fn {r, i} -> r["index"] == i end) and
           outlives == expected

  defp params?(_, _, _), do: false

  defp outlives,
    do: %{"regions" => [], "outlives" => [], "skip_binder" => [%{"Lub" => variable()}, region()]}

  defp region, do: %{"Var" => %{"Free" => 0}}
  defp variable, do: %{"TypeVar" => %{"Free" => 0}}

  defp arguments(types, regions \\ []),
    do: %{"regions" => regions, "types" => types, "const_generics" => [], "trait_refs" => []}

  defp adt(id, types, regions \\ []),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments(types, regions)}}

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
