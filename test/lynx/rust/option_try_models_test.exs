defmodule Lynx.Rust.OptionTryModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.TryModels
  @fixture Path.expand("../../fixtures/rust_workspace/option_try_metadata.json", __DIR__)
  # Trimmed, expanded metadata captured from the pinned compiler's Option ? path.
  @translated JSON.decode!(File.read!(@fixture))

  test "admits the exact standard Option Try and Never residual operations" do
    for function <- @translated["fun_decls"] do
      assert %{builtin: false, can_fail: false, lift: true, native_transfer: true} =
               TryModels.resolve(function, @translated, %{})

      for changed <- [
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "abi"], "C"),
            put_in(function, ["signature", "is_variadic"], true),
            put_in(function, ["signature", "inputs"], []),
            put_in(function, ["signature", "output"], "Never"),
            put_in(function, ["src", "TraitImpl", "reuses_default"], true),
            put_in(function, ["src", "TraitImpl", "item_id"], 99),
            Map.put(function, "body", %{"Intrinsic" => %{"name" => "assume"}}),
            Map.put(function, "def_id", 999)
          ],
          do: assert(is_nil(TryModels.resolve(changed, @translated, %{})))

      for key <- ~w(trait_impls trait_decls type_decls) do
        assert is_nil(TryModels.resolve(function, Map.put(@translated, key, []), %{}))
      end

      for {type, index} <- Enum.with_index(@translated["type_decls"]),
          List.last(type["item_meta"]["name"]) == %{"Ident" => ["Option", 0]} or
            List.last(function["item_meta"]["name"]) == %{"Ident" => ["branch", 0]} do
        changed =
          update_in(
            @translated,
            ["type_decls", Access.at(index), "kind", "Enum"],
            &Enum.reverse/1
          )

        assert is_nil(TryModels.resolve(function, changed, %{}))
      end
    end
  end

  test "a payload-bearing residual cannot masquerade as Option Never" do
    for function <- @translated["fun_decls"] do
      changed = replace_never(function)
      refute changed == function
      assert is_nil(TryModels.resolve(changed, @translated, %{}))
    end
  end

  defp replace_never("Never"), do: %{"TypeVar" => %{"Free" => 0}}
  defp replace_never(value) when is_list(value), do: Enum.map(value, &replace_never/1)

  defp replace_never(value) when is_map(value),
    do: Map.new(value, fn {key, entry} -> {key, replace_never(entry)} end)

  defp replace_never(value), do: value
end
