defmodule Lynx.Rust.ExternalModelsTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @moduletag timeout: 300_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for external-model admission tests")

  @tag :tmp_dir
  test "external model options cannot replace first-party implementations", %{tmp_dir: tmp} do
    options = [
      tools: @tools,
      roots: ["experiment_core::order_pair"],
      build_dir: Path.join(tmp, "build"),
      lean_project: Path.join(tmp, "proofs"),
      module_prefix: "ExternalAdmission.Extraction",
      external_types: [
        %{
          rust: "experiment_core::order_pair",
          lean: "Bool",
          import: "Init",
          label: "Deliberate forbidden first-party replacement"
        }
      ]
    ]

    assert_raise ArgumentError, ~r/first-party type replacement/, fn ->
      Lynx.Rust.verify!(@fixture, "experiment-core", options)
    end

    assert_raise ArgumentError, ~r/unknown external Rust call model/, fn ->
      options =
        options
        |> Keyword.delete(:external_types)
        |> Keyword.put(:external_calls, [:trust_anything])

      Lynx.Rust.verify!(@fixture, "experiment-core", options)
    end
  end
end
