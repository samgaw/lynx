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
           %{"Ident" => [method, 0]}
         ] <- name,
         true <- [a, b, c] == path(~w(std sync poison)),
         family <- if(d == %{"Ident" => ["mutex", 0]}, do: :mutex, else: :rwlock),
         true <- d == %{"Ident" => [if(family == :mutex, do: "mutex", else: "rwlock"), 0]},
         true <- {family, method} in [{:mutex, "lock"}, {:rwlock, "read"}, {:rwlock, "write"}],
         true <- params?(parent_params, 0, []),
         true <- params?(CallModels.expand(params, refs), 1, [outlives()]),
         %{"Adt" => %{"id" => mutex, "builtin" => nil, "generics" => args}} <-
           CallModels.expand(parent, refs),
         true <- args == arguments([%{"TypeVar" => %{"Bound" => [0, 0]}}]),
         true <-
           Enum.any?(
             translated["type_decls"],
             &(&1 && &1["def_id"] == mutex &&
                 if(family == :mutex,
                   do: MutexModels.type?(&1),
                   else: Lynx.Rust.RwLockModels.type?(&1)
                 ))
           ),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Ref" => [region(), adt(mutex, [variable()]), "Shared"]}
           ],
         kind =
           if(family == :mutex,
             do: :mutex,
             else: if(method == "read", do: :rw_read, else: :rw_write)
           ),
         guard when not is_nil(guard) <-
           Enum.find(translated["type_decls"], &(guard_kind(&1, refs) == kind)),
         poison when not is_nil(poison) <- Enum.find(translated["type_decls"], &poison?/1),
         %{"Adt" => %{"id" => result, "generics" => result_args, "builtin" => nil}} <-
           CallModels.expand(sig["output"], refs),
         true <- LLBC.result_type?(result, %{translated: translated, references: refs}),
         guard_type = adt(guard["def_id"], [variable()], [region()]),
         true <- result_args == arguments([guard_type, adt(poison["def_id"], [guard_type])]) do
      %{
        rust_name:
          "std::sync::poison::#{family}::{std::sync::poison::#{family}::#{if family == :mutex, do: "Mutex", else: "RwLock"}<@T>}::#{method}",
        lean: "Lynx.#{if family == :mutex, do: "NativeMutex", else: "NativeRwLock"}.#{method}",
        builtin: false,
        can_fail: true,
        native_cutoff_only: true,
        lift: true,
        native_lock_type: mutex,
        native_guard_kind: kind,
        native_guard_type: guard["def_id"],
        native_poison_type: poison["def_id"],
        native_codec_input: true,
        label:
          "Blocking Mutex::lock model: atomic shared-cell acquisition; poisoned acquisition returns an owned guard in PoisonError; recursive acquisition and malformed identities exhaust verification; logical execution contexts are local Lynx processes; native async/thread migration, Rust std and FFI implementation correctness unverified"
      }
      |> Map.put(if(family == :mutex, do: :native_mutex_type, else: :native_rwlock_type), mutex)
      |> then(fn model ->
        if family == :mutex,
          do: model,
          else:
            Map.put(
              model,
              :label,
              "Logical blocking std RwLock::#{method} model: shared reader leases or an exclusive writer; a conflicting foreign owner blocks, queued writers retain typed context-bound request tickets, and successful acquisition removes its own ticket atomically; poisoned acquisition returns the acquired guard in PoisonError; new reads with a queued writer, self-conflicting acquisition, invalid tickets and reader-limit exhaustion are verification cutoffs; OS priority, fairness, native thread correspondence, std and FFI correctness remain unverified"
            )
      end)
    else
      _ -> nil
    end
  end

  def guard?(type, refs), do: guard_kind(type, refs) != nil

  def guard_kind(
        %{
          "src" => "Normal",
          "kind" => "Opaque",
          "generics" => params,
          "item_meta" => %{"name" => name}
        },
        refs
      ) do
    params = CallModels.expand(params, refs)

    cond do
      name == path(@base ++ ["MutexGuard"]) and params?(params, 1, [outlives(), outlives()]) ->
        :mutex

      name == path(~w(std sync poison rwlock RwLockReadGuard)) and
          params?(params, 1, [outlives()]) ->
        :rw_read

      name == path(~w(std sync poison rwlock RwLockWriteGuard)) and
          params?(params, 1, [outlives(), outlives()]) ->
        :rw_write

      true ->
        nil
    end
  end

  def guard_kind(_, _), do: nil

  def guard_name(:mutex), do: "MutexGuard"
  def guard_name(:rw_read), do: "RwLockReadGuard"
  def guard_name(:rw_write), do: "RwLockWriteGuard"
  def guard_module(:mutex), do: "NativeGuard"
  def guard_module(:rw_read), do: "NativeRwReadGuard"
  def guard_module(:rw_write), do: "NativeRwWriteGuard"
  def guard_path(:mutex), do: path(@base ++ ["MutexGuard"])

  def guard_path(kind) when kind in [:rw_read, :rw_write],
    do: path(~w(std sync poison rwlock) ++ [guard_name(kind)])

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

    guards =
      for kind <- [:mutex, :rw_read, :rw_write],
          Enum.any?(models, fn {_, model} ->
            (model[:native_guard_type] != nil and
               Map.get(model, :native_guard_kind, :mutex) == kind) or
              kind in Map.get(model, :native_guard_kinds, [])
          end),
          do: %{
            rust: Enum.map_join(guard_path(kind), "::", fn %{"Ident" => [part, 0]} -> part end),
            lean: "Lynx." <> guard_module(kind),
            import: module,
            label:
              "Validated standard guard identity and borrowed view; ownership audited separately; std/native layout and FFI unverified"
          }

    poison =
      if Enum.any?(models, fn {_, model} -> model[:native_poison_type] end),
        do: [
          %{
            rust: "std::sync::poison::PoisonError",
            lean: "Lynx.NativePoisonError",
            import: module,
            label:
              "Poisoned acquisition retains the acquired guard; std/native layout and FFI unverified"
          }
        ],
        else: []

    guards ++ poison
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
