defmodule Lynx.Rust.GuardedRecoveryTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_FILE_AWAIT_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_FILE_AWAIT_DIR for guarded future crash and recovery proofs")

  @tag :tmp_dir
  test "verifies future acknowledgements across crash and actual reopened recovery", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "GuardedRecovery"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    for {source, target} <- [
          {"GuardedRecoveryProperties.lean", "Properties.lean"},
          {"GuardedRecoveryWriterProperties.lean", "Writer.lean"}
        ],
        do:
          File.cp!(Path.join(@fixture, source), Path.join(project, "GuardedRecovery/" <> target))

    properties =
      ~w(GuardedRecovery.Properties.recovery_after_restart
      GuardedRecovery.Properties.every_recovery GuardedRecovery.Writer.writer_transitions
      GuardedRecovery.Writer.failed_sync_can_lose_writes GuardedRecovery.Writer.acknowledged_recovery
      GuardedRecovery.Writer.every_acknowledged_recovery)

    options = [
      roots: ~w(io_protocol::reopen_words io_protocol::poll_locked_sync),
      tools: @tools,
      execution: :runtime,
      files: :regular,
      futures: :cancelling,
      owned_drops: true,
      branching: :duplicate,
      lean_project: project,
      module_prefix: "GuardedRecovery.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["GuardedRecovery.Properties", "GuardedRecovery.Writer"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports
    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: properties
      )

    export = Path.join(tmp, "guarded.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(workspace, "protocol/src/lib.rs")
    valid = File.read!(source)

    for {marker, from, to} <- [
          {"pub fn reopen_words(", "locked_word(&mutex, 2)", "locked_word(&mutex, 0)"},
          {"fn synchronize_written(", "        Ok(count) => match",
           "        Ok(2) => Ok(2),\n        Ok(count) => match"}
        ] do
      [prefix, body] = String.split(valid, marker, parts: 2)
      changed = String.replace(body, from, to, global: false)
      refute body == changed
      File.write!(source, prefix <> marker <> changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

      File.write!(source, valid)
      assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
    end

    proof = Path.join(project, "GuardedRecovery/Writer.lean")
    valid_proof = File.read!(proof)

    for extra <- [
          "private axiom assumed_crash_image : False",
          "private theorem unfinished_recovery : True := by sorry"
        ] do
      File.write!(proof, valid_proof <> "\n" <> extra)

      assert_raise RuntimeError, ~r/proof audit failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end
    end

    File.write!(proof, valid_proof)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
