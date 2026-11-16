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
          {"GuardedRecoveryWriterProperties.lean", "Writer.lean"},
          {"GuardedReadTraceProperties.lean", "ReadTrace.lean"},
          {"ReadTraceCompleteness.lean", "ReadCompleteness.lean"},
          {"LockedTraceCompleteness.lean", "LockedCompleteness.lean"},
          {"RecoveryTraceProperties.lean", "RecoveryTrace.lean"}
        ],
        do:
          File.write!(
            Path.join(project, "GuardedRecovery/" <> target),
            File.read!(Path.join(@fixture, source))
            |> String.replace("io_native io_native.io_protocol", "io_protocol")
          )

    properties =
      ~w(GuardedRecovery.Properties.recovery_after_restart
      GuardedRecovery.Properties.every_recovery GuardedRecovery.Writer.writer_transitions
      GuardedRecovery.Writer.failed_sync_can_lose_writes GuardedRecovery.Writer.acknowledged_recovery
      GuardedRecovery.Writer.every_acknowledged_recovery
      GuardedRecovery.ReadTrace.Reads.ready GuardedRecovery.ReadTrace.locked_contract
      GuardedRecovery.ReadTrace.locked_ready GuardedRecovery.ReadTrace.locked_every_run
      GuardedRecovery.ReadTrace.admitted_locked GuardedRecovery.ReadTrace.missing_error_exhausts
      GuardedRecovery.ReadCompleteness.reads_complete GuardedRecovery.ReadCompleteness.completed_iff
      GuardedRecovery.LockedCompleteness.locked_complete GuardedRecovery.LockedCompleteness.locked_iff
      GuardedRecovery.RecoveryTrace.reopen_contract GuardedRecovery.RecoveryTrace.Reopens.ready
      GuardedRecovery.RecoveryTrace.Reopens.every_final_state
      GuardedRecovery.RecoveryTrace.admitted_execution GuardedRecovery.RecoveryTrace.admitted_every_run)

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
      proof_modules: [
        "GuardedRecovery.Properties",
        "GuardedRecovery.Writer",
        "GuardedRecovery.ReadTrace",
        "GuardedRecovery.ReadCompleteness",
        "GuardedRecovery.LockedCompleteness",
        "GuardedRecovery.RecoveryTrace"
      ],
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

    for {label, marker, from, to} <- [
          {"offset", "pub fn reopen_words(", "locked_word(&mutex, 2)", "locked_word(&mutex, 0)"},
          {"endian", "pub fn read_word(", "from_le_bytes([low, high])",
           "from_le_bytes([high, low])"},
          {"error_code", "pub fn locked_word(", "Err(1)", "Err(2)"},
          {"open_error", "pub fn reopen_words(", "Err(3)", "Err(4)"},
          {"sync", "fn synchronize_written(", "        Ok(count) => match",
           "        Ok(2) => Ok(2),\n        Ok(count) => match"}
        ] do
      [prefix, body] = String.split(valid, marker, parts: 2)
      changed = String.replace(body, from, to, global: false)
      refute body == changed
      File.write!(source, prefix <> marker <> changed)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      if marker in ["pub fn read_word(", "pub fn locked_word("] do
        assert error.message =~ "ReadTrace.lean"
        assert error.message =~ ~r/unsolved goals|Type mismatch|Tactic|rfl/
      end

      if label == "open_error" do
        assert error.message =~ "RecoveryTrace.lean"
        assert error.message =~ ~r/unsolved goals|Type mismatch|Tactic|rfl/
      end

      File.write!(Path.join(tmp, "mutation-" <> label <> ".log"), error.message)

      File.write!(source, valid)
      assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
    end

    proof = Path.join(project, "GuardedRecovery/RecoveryTrace.lean")
    valid_proof = File.read!(proof)

    wrong_cleanup =
      String.replace(valid_proof, ".nil false true", ".nil false false", global: false)

    refute wrong_cleanup == valid_proof
    File.write!(proof, wrong_cleanup)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "RecoveryTrace.lean"
    assert error.message =~ ~r/unsolved goals|Type mismatch|Tactic|rfl/
    File.write!(Path.join(tmp, "wrong-cleanup.log"), error.message)
    File.write!(proof, valid_proof)

    completeness = Path.join(project, "GuardedRecovery/ReadCompleteness.lean")
    valid_completeness = File.read!(completeness)

    [helpers, characterization] =
      String.split(valid_completeness, "theorem completed_iff", parts: 2)

    wrong_eof =
      String.replace(
        characterization,
        "returnedFile = file ∧ Reads",
        "returnedFile = file ∧ reply = .Ok none ∧ Reads"
      )

    refute wrong_eof == characterization
    File.write!(completeness, helpers <> "theorem completed_iff" <> wrong_eof)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "ReadCompleteness.lean"
    assert error.message =~ ~r/unsolved goals|Type mismatch|Tactic|rfl/
    File.write!(Path.join(tmp, "wrong-read-classification.log"), error.message)
    File.write!(completeness, valid_completeness)

    locked = Path.join(project, "GuardedRecovery/LockedCompleteness.lean")
    valid_locked = File.read!(locked)
    [helpers, characterization] = String.split(valid_locked, "theorem locked_complete", parts: 2)

    wrong_poison =
      String.replace(
        characterization,
        "∧\n      Critical",
        "∧\n      (∃ guard, reply = .Ok guard) ∧ Critical",
        global: false
      )

    refute wrong_poison == characterization
    File.write!(locked, helpers <> "theorem locked_complete" <> wrong_poison)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "LockedCompleteness.lean"
    assert error.message =~ ~r/unsolved goals|Type mismatch|Tactic|rfl/
    File.write!(Path.join(tmp, "wrong-poison-classification.log"), error.message)
    File.write!(locked, valid_locked)

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

    for extra <- [
          "private axiom assumed_read_outcome : False",
          "private theorem unfinished_read : True := by sorry"
        ] do
      File.write!(completeness, valid_completeness <> "\n" <> extra)

      assert_raise RuntimeError, ~r/proof audit failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end
    end

    File.write!(completeness, valid_completeness)

    for extra <- [
          "private axiom assumed_lock_acquisition : False",
          "private theorem unfinished_lock : True := by sorry"
        ] do
      File.write!(locked, valid_locked <> "\n" <> extra)

      assert_raise RuntimeError, ~r/proof audit failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end
    end

    File.write!(locked, valid_locked)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
