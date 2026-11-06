defmodule Lynx.Rustler.OwnedResourceConfigurationTest do
  use ExUnit.Case, async: true

  test "requires runtime execution and an explicit boolean cleanup selection" do
    for options <- [[owned_drops: true], [execution: :runtime, owned_drops: :all]] do
      assert_raise ArgumentError, ~r/owned resource cleanup requires runtime execution/, fn ->
        Lynx.Rustler.prepare!("/unused", "unused", options)
      end
    end

    manifest = %{module: "Elixir.OwnedResourceConfiguration", bindings: [], exports: []}

    for options <- [[owned_drops: true], [execution: :runtime, owned_drops: :all]] do
      assert_raise ArgumentError, ~r/owned resource cleanup requires runtime execution/, fn ->
        Lynx.Rustler.Adapter.external!(
          manifest,
          %{},
          options ++
            [
              bridge_module: "Owned.Bridge",
              implementation_module: "Owned.InvalidAdapter"
            ]
        )
      end
    end
  end
end
