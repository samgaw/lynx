defmodule Lynx.Rust.FutureModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  def resolve(
        %{
          "body" => "Opaque",
          "src" => "Normal",
          "signature" =>
            %{
              "is_unsafe" => false,
              "is_variadic" => false,
              "abi" => "Rust"
            } = sig,
          "generics" => params,
          "item_meta" => %{"name" => name}
        },
        translated,
        refs
      ) do
    with [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["task", 0]},
           %{"Ident" => ["wake", 0]},
           %{"Impl" => %{"Ty" => %{"kind" => "InherentImplBlock", "skip_binder" => parent}}},
           %{"Ident" => [method, 0]}
         ] <- name,
         context when not is_nil(context) <- type(translated, "Context"),
         waker when not is_nil(waker) <- type(translated, "Waker") do
      context_id = context["def_id"]
      waker_id = waker["def_id"]
      parent = CallModels.expand(parent, refs)
      input = CallModels.expand(sig["inputs"], refs)
      output = CallModels.expand(sig["output"], refs)

      common =
        params["types"] == [] and params["const_generics"] == [] and params["trait_clauses"] == [] and
          params["trait_type_constraints"] == []

      cond do
        method == "noop" and common and params["regions"] == [] and input == [] and
          output == %{"Ref" => ["Static", adt(waker_id), "Shared"]} and
            parent == adt(waker_id) ->
          %{
            rust_name: "core::task::wake::{core::task::wake::Waker}::noop",
            lean: "Lynx.NativeWaker.noop",
            native_wake_operation: :noop,
            builtin: false,
            can_fail: false,
            lift: false,
            label:
              "Standard Waker::noop model: nonallocating static waker whose callbacks do nothing; no notification or progress guarantee; std implementation, pointer layout and native vtable correctness remain trusted"
          }

        method == "from_waker" and common and length(params["regions"]) == 1 and
          input == [ref(0, adt(waker_id))] and output == adt(context_id, [region(0)]) and
            parent == adt(context_id, [%{"Var" => %{"Bound" => [0, 0]}}]) ->
          %{
            rust_name: "core::task::wake::{core::task::wake::Context<'a>}::from_waker",
            lean: "Lynx.NativeTaskContext.fromWaker",
            native_wake_operation: :from_waker,
            builtin: false,
            can_fail: false,
            lift: false,
            label:
              "Standard Context::from_waker model: retain the supplied borrowed waker; unsupported local-waker/extension observations remain rejected; std constructor and physical Context layout unverified"
          }

        method == "waker" and common and length(params["regions"]) == 2 and
          input == [ref(1, adt(context_id, [region(0)]))] and output == ref(0, adt(waker_id)) and
            parent == adt(context_id, [%{"Var" => %{"Bound" => [0, 0]}}]) ->
          %{
            rust_name: "core::task::wake::{core::task::wake::Context<'a>}::waker",
            lean: "Lynx.NativeTaskContext.waker",
            native_wake_operation: :context_waker,
            builtin: false,
            can_fail: false,
            lift: false,
            label:
              "Context::waker identity model for registered or standard no-op wakers; native Context layout and callback registration unverified"
          }

        method == "wake_by_ref" and common and length(params["regions"]) == 1 and
          input == [ref(0, adt(waker_id))] and
          output == %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args([])}} and
            parent == adt(waker_id) ->
          %{
            rust_name: "core::task::wake::{core::task::wake::Waker}::wake_by_ref",
            lean: "Lynx.NativeWaker.wakeByRef",
            native_wake_operation: :wake_by_ref,
            builtin: false,
            can_fail: true,
            lift: true,
            native_cutoff_only: true,
            label:
              "Waker::wake_by_ref dispatch model: standard no-op discards requests without effects; registered nonpanicking callbacks atomically coalesce notifications; invalid capabilities exhaust verification; physical vtables, callback implementation, allocation and executor scheduling unverified"
          }

        true ->
          nil
      end
    else
      _ -> nil
    end
  end

  def resolve(_, _, _), do: nil

  def type(translated, name) do
    case Enum.filter(translated["type_decls"], &(&1 && &1["item_meta"]["name"] == path(name))) do
      [
        %{
          "src" => "Normal",
          "kind" => "Opaque",
          "generics" => %{
            "types" => [],
            "const_generics" => [],
            "trait_clauses" => [],
            "trait_type_constraints" => [],
            "regions" => regions
          }
        } = type
      ]
      when (name == "Context" and length(regions) == 1) or (name == "Waker" and regions == []) ->
        type

      _ ->
        nil
    end
  end

  defp path(name), do: Enum.map(["core", "task", "wake", name], &%{"Ident" => [&1, 0]})
  defp region(index), do: %{"Var" => %{"Free" => index}}
  defp ref(index, type), do: %{"Ref" => [region(index), type, "Shared"]}

  defp args(regions),
    do: %{"regions" => regions, "types" => [], "const_generics" => [], "trait_refs" => []}

  defp adt(id, regions \\ []),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args(regions)}}
end
