defmodule Lynx.Rustler.SharedRecoveryTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for shared-inode recovery proofs")

  @tag :tmp_dir
  test "composes extracted recovery with shared inode and resource ownership", %{tmp_dir: tmp} do
    %{options: options, project: project} =
      Lynx.Rust.IoFixture.prepare_shared!(tmp, @tools, [
        "ConcurrentStorageProperties",
        "SharedRecoveryProperties",
        "ConcurrentRecoveryProperties",
        "SharedReadProperties",
        "SharedFilesystemProperties"
      ])

    properties = [
      "Record.SharedRecoveryProperties.recover_shared_log",
      "Record.SharedRecoveryProperties.constructed_log_recovery",
      "Record.ConcurrentRecoveryProperties.accepted_recovery",
      "Record.ConcurrentRecoveryProperties.checked_recovery",
      "Record.SharedReadProperties.recover_reopened_log",
      "Record.SharedReadProperties.open_named_log",
      "Record.SharedReadProperties.named_log_restart",
      "Record.SharedFilesystemProperties.constructed_filesystem_recovery"
    ]

    options = Keyword.update!(options, :required_properties, &(&1 ++ properties))
    prepared = Lynx.Rustler.prepare!(options)

    for property <- properties do
      assert Enum.any?(prepared.verification.guarantees, &(Map.get(&1, :theorem) == property))
    end

    for name <- ~w(SharedRecoveryProperties SharedReadProperties SharedFilesystemProperties) do
      source = Path.join(project, "Record/" <> name <> ".lean")
      original = File.read!(source)

      # Reversing the claimed payloads must fail for both the independent restart
      # and the reopened shared-descriptor implementation of the Rust loop.
      wrong =
        String.replace(original, "alloc.vec.Vec.from values", "alloc.vec.Vec.from values.reverse")

      refute wrong == original
      File.write!(source, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(source, original)
      assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
    end

    source = Path.join(project, "Record/SharedFilesystemProperties.lean")
    original = File.read!(source)

    wrong =
      String.replace(
        original,
        "some ⟨Record.ConstructorLogProperties.names,[(1,state.visible)],counter⟩",
        "some ⟨[],[(1,state.visible)],counter⟩"
      )

    refute wrong == original
    File.write!(source, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(source, original)
    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end
end
