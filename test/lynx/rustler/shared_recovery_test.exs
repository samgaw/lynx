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
        "ConcurrentRecoveryProperties"
      ])

    properties = [
      "Record.SharedRecoveryProperties.recover_shared_log",
      "Record.SharedRecoveryProperties.constructed_log_recovery",
      "Record.ConcurrentRecoveryProperties.accepted_recovery",
      "Record.ConcurrentRecoveryProperties.checked_recovery"
    ]

    options = Keyword.update!(options, :required_properties, &(&1 ++ properties))
    prepared = Lynx.Rustler.prepare!(options)

    for property <- properties do
      assert Enum.any?(prepared.verification.guarantees, &(Map.get(&1, :theorem) == property))
    end

    source = Path.join(project, "Record/SharedRecoveryProperties.lean")
    original = File.read!(source)

    # Reversing the claimed recovered payloads is false for general logs. The
    # existing proof must fail against the actual extracted recovery loop.
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
end
