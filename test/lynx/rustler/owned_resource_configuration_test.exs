defmodule Lynx.Rustler.OwnedResourceConfigurationTest do
  use ExUnit.Case, async: true

  test "file models are explicit and require runtime execution before building" do
    assert_raise ArgumentError, ~r/regular-file models require runtime execution/, fn ->
      Lynx.Rustler.prepare!("/unused", "unused", files: :regular)
    end

    assert_raise ArgumentError, ~r/unsupported Rust file model/, fn ->
      Lynx.Rustler.prepare!("/unused", "unused", execution: :runtime, files: :all)
    end
  end

  test "separates runtime resource cleanup from pure explicit destruction" do
    for options <- [
          [owned_drops: true],
          [execution: :runtime, owned_drops: :all],
          [execution: :runtime, owned_drops: :explicit]
        ] do
      assert_raise ArgumentError, ~r/owned resource cleanup requires runtime execution/, fn ->
        Lynx.Rustler.prepare!("/unused", "unused", options)
      end
    end

    manifest = %{module: "Elixir.OwnedResourceConfiguration", bindings: [], exports: []}

    for options <- [
          [owned_drops: true],
          [execution: :runtime, owned_drops: :all],
          [execution: :runtime, owned_drops: :explicit]
        ] do
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
