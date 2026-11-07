defmodule Lynx.Rust.FileAppendTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "native-loops-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native-loops backend")

  @tag :tmp_dir
  test "verifies actual append, multi-record native loops and crash recovery", %{tmp_dir: tmp} do
    {workspace, project, base} = Lynx.Rust.IoFixture.prepare!(tmp, @tools)

    proof_options = [
      required_properties:
        Enum.map(
          ~w(encode_spec decode_spec decode_layout write_record_ready torn_decode record_ready record_torn four_reads recover_four recover_torn_default),
          &("Record.IntegrityProperties." <> &1)
        ) ++
          Enum.map(
            ~w(truncated_reads truncated_data recover_truncated recover_prefix recover_fresh crash_recovery write_record_success recover_encoded write_record_crash write_once_crash),
            &("Record.CrashProperties." <> &1)
          ) ++
          Enum.map(
            ~w(recover_log_two append_ready append_success append_crash_prefix append_pair_recovery),
            &("Record.AppendProperties." <> &1)
          ) ++
          Enum.map(
            ~w(recover_encoded_log stable_log_recovery append_log_recovery),
            &("Record.LogProperties." <> &1)
          ) ++
          Enum.map(
            ~w(recover_truncated_log restart_truncated_log retry_during_scan),
            &("Record.TailProperties." <> &1)
          ) ++
          Enum.map(
            ~w(resize_success_next resize_failure resize_sync_failure resize_outside repair_success repair_limit repair_crash unsynced_shrink repair_default),
            &("Record.ResizeProperties." <> &1)
          ) ++
          Enum.map(
            ~w(repair_prepare repair_at_sync crash_retry restart_repair repair_interrupt),
            &("Record.RepairCrashProperties." <> &1)
          ) ++
          Enum.map(
            ~w(malformed_at recover_malformed_next recover_malformed repair_malformed repair_malformed_default repair_malformed_crash),
            &("Record.MalformedProperties." <> &1)
          ) ++
          Enum.map(
            ~w(critical_contract append_contract locked_ready locked_success critical_error_steps contention_waits),
            &("Record.LockedProperties." <> &1)
          ) ++
          [
            "Record.LockedConcurrent.appends_interleave",
            "Record.LockedConcurrent.appends_all_schedules",
            "Record.LockedConcurrent.error_then_append_all_schedules",
            "Record.RollbackProperties.append_contract",
            "Record.RollbackProperties.critical_contract",
            "Record.RollbackProperties.rollback_then_append_all_schedules",
            "Record.RollbackProperties.rollback_resize_failure",
            "Record.RollbackProperties.rollback_sync_failure",
            "Record.RollbackProperties.rollback_failure_effects",
            "Record.InterruptedProperties.concurrent_rollback_stalls",
            "Record.InterruptedProperties.concurrent_crash_image",
            "Record.InterruptedProperties.concurrent_crash_repair",
            "Record.TornConcurrent.torn_rollback_stalls",
            "Record.TornConcurrent.torn_crash_repair",
            "Record.TornConcurrent.persisted_tail_images",
            "Record.WriteInterrupted.before_resize_stalls",
            "Record.WriteInterrupted.before_resize_crash_repair",
            "Record.WriteInterrupted.before_resize_images"
          ]
    ]

    options = base ++ proof_options

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert [
             %{
               "status" => :modelled,
               "implementation_verified" => false,
               "lean_name" => "Aeneas.Std.core.num.U16.MAX"
             }
           ] = result.verification.constants

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "initializer not implementation verified")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.IntegrityProperties.recover_torn_default")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.CrashProperties.write_once_crash")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "integrity.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    assert [%{kind: :native_loop, iterations: 262_145, exhausted: :verification_cutoff}] =
             result.verification.verification_bounds

    assert [%{type: "alloc::vec::Vec<u16>", status: :modelled, implementation_verified: false}] =
             result.verification.structural_drops

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.AppendProperties.append_pair_recovery")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.LogProperties.append_log_recovery")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.TailProperties.retry_during_scan")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.ResizeProperties.repair_crash")
           )

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "successful set_len does not guarantee persistence")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.RepairCrashProperties.repair_interrupt")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.MalformedProperties.repair_malformed_crash")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.LockedProperties.locked_success")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.LockedConcurrent.appends_interleave")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.LockedConcurrent.appends_all_schedules")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.LockedConcurrent.error_then_append_all_schedules")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.RollbackProperties.rollback_then_append_all_schedules")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.InterruptedProperties.concurrent_crash_repair")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.TornConcurrent.torn_crash_repair")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.WriteInterrupted.before_resize_crash_repair")
           )

    for target <- [
          "Record/AppendProperties.lean",
          "Record/LogProperties.lean",
          "Record/TailProperties.lean",
          "Record/ResizeProperties.lean",
          "Record/RepairCrashProperties.lean",
          "Record/MalformedProperties.lean",
          "Record/LockedProperties.lean",
          "Record/LockedConcurrent.lean",
          "Record/RollbackProperties.lean",
          "Record/InterruptedProperties.lean",
          "Record/TornConcurrent.lean",
          "Record/WriteInterrupted.lean",
          "Record/Extraction/VectorModel.lean"
        ] do
      path = Path.join(project, target)
      source = File.read!(path)

      for extra <- [
            "private axiom logTrust : False",
            "private theorem unfinishedLog : True := by sorry"
          ] do
        File.write!(path, source <> "\n" <> extra <> "\n")
        Project.build!(project, options[:proof_modules])
        assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
        File.write!(path, source)
      end
    end

    property = Path.join(project, "Record/LogProperties.lean")
    correct = File.read!(property)

    wrong =
      String.replace(
        correct,
        "(4 * values.length)) frame) := by",
        "(4 * values.length + 1)) frame) := by",
        global: false
      )

    refute wrong == correct
    File.write!(property, wrong)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Project.build!(project, options[:proof_modules])
      end

    assert error.message =~ "Record/LogProperties.lean:"
    File.write!(property, correct)

    property = Path.join(project, "Record/RepairCrashProperties.lean")
    correct = File.read!(property)

    premature =
      String.replace(
        correct,
        "⟨disk (logBytes values), durable,",
        "⟨disk (logBytes values), disk (logBytes values),",
        global: false
      )

    refute premature == correct
    File.write!(property, premature)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Project.build!(project, options[:proof_modules])
      end

    assert error.message =~ "Record/RepairCrashProperties.lean:"
    File.write!(property, correct)

    property = Path.join(project, "Record/LockedConcurrent.lean")
    correct = File.read!(property)

    lost =
      String.replace(
        correct,
        "data.data.toList ++ (encoded first).data.toList ++ (encoded second).data.toList",
        "data.data.toList ++ (encoded second).data.toList",
        global: false
      )

    refute lost == correct
    File.write!(property, lost)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Project.build!(project, options[:proof_modules])
      end

    assert error.message =~ "Record/LockedConcurrent.lean:"
    File.write!(property, correct)

    ordered =
      String.replace(
        correct,
        "(.ok Term.true, shared 4 free (appended nextSecond first rest))",
        "(.ok Term.true, shared 4 free (appended nextFirst second rest))",
        global: false
      )

    refute ordered == correct
    File.write!(property, ordered)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Project.build!(project, options[:proof_modules])
      end

    assert error.message =~ "Record/LockedConcurrent.lean:"
    File.write!(property, correct)

    hidden_error =
      String.replace(
        correct,
        "(.ok (errorTerm errorId), shared 4 free (appended next second rest))",
        "(.ok Term.true, shared 4 free (appended next second rest))",
        global: false
      )

    refute hidden_error == correct
    File.write!(property, hidden_error)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Project.build!(project, options[:proof_modules])
      end

    assert error.message =~ "Record/LockedConcurrent.lean:"
    File.write!(property, correct)

    property = Path.join(project, "Record/RollbackProperties.lean")
    correct = File.read!(property)

    for broken <- [
          String.replace(
            correct,
            "⟨if syncFailure then ByteArray.empty else ⟨#[1, 0]⟩, ⟨#[1, 0]⟩, 2, rest⟩",
            "⟨if syncFailure then ByteArray.empty else ⟨#[1, 0]⟩, ByteArray.empty, 2, rest⟩"
          ),
          String.replace(
            correct,
            "(.ok (errorTerm errorId), shared 3 free after)",
            "(.ok Term.false, shared 3 free after)"
          )
        ] do
      refute broken == correct
      File.write!(property, broken)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Project.build!(project, options[:proof_modules])
        end

      assert error.message =~ "Record/RollbackProperties.lean:"
      File.write!(property, correct)
    end

    property = Path.join(project, "Record/InterruptedProperties.lean")
    correct = File.read!(property)

    for broken <- [
          correct
          |> String.replace(
            "(.deadlock, shared 3 (owned 1 3) (stopped data amount rest))",
            "(.deadlock, shared 3 free (stopped data amount rest))"
          )
          |> String.replace(
            "(.deadlock, shared 3 (owned 2 3) (stopped data amount rest))",
            "(.deadlock, shared 3 free (stopped data amount rest))"
          ),
          String.replace(
            correct,
            "some (alloc.vec.Vec.from values (by scalar_tac))",
            "some (alloc.vec.Vec.from [] (by scalar_tac))"
          )
        ] do
      refute broken == correct
      File.write!(property, broken)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Project.build!(project, options[:proof_modules])
        end

      assert error.message =~ "Record/InterruptedProperties.lean:"
      File.write!(property, correct)
    end

    property = Path.join(project, "Record/TornConcurrent.lean")
    correct = File.read!(property)

    for broken <- [
          correct
          |> String.replace(
            "some (⟨crop (encoded first) 2, 3⟩ : Image)",
            "some (⟨ByteArray.empty, 3⟩ : Image)"
          )
          |> String.replace(
            "some (⟨crop (encoded second) 2, 3⟩ : Image)",
            "some (⟨ByteArray.empty, 3⟩ : Image)"
          ),
          String.replace(
            correct,
            "some (alloc.vec.Vec.from values (by scalar_tac))",
            "some (alloc.vec.Vec.from [] (by scalar_tac))"
          )
        ] do
      refute broken == correct
      File.write!(property, broken)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Project.build!(project, options[:proof_modules])
        end

      assert error.message =~ "Record/TornConcurrent.lean:"
      File.write!(property, correct)
    end

    property = Path.join(project, "Record/WriteInterrupted.lean")
    correct = File.read!(property)

    for broken <- [
          String.replace(
            correct,
            "⟨overwrite data data.size (bytes (payload value)) amount,",
            "⟨data,"
          ),
          String.replace(
            correct,
            "some (alloc.vec.Vec.from values (by scalar_tac))",
            "some (alloc.vec.Vec.from [] (by scalar_tac))"
          )
        ] do
      refute broken == correct
      File.write!(property, broken)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Project.build!(project, options[:proof_modules])
        end

      assert error.message =~ "Record/WriteInterrupted.lean:"
      File.write!(property, correct)
    end

    source = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(source)

    for {broken, proof} <- [
          {String.replace(rust, "resize_then_sync(file, start)", "resize_then_sync(file, 0)"),
           "RollbackProperties"},
          {String.replace(
             rust,
             "resize_then_sync(file, start)",
             "io_core::resize_to(file, start)"
           ), "RollbackProperties"},
          {String.replace(
             rust,
             ~r/pub fn write_then_sync\(.*?\n\}/s,
             """
             pub fn write_then_sync(file: &mut File, bytes: &[u8]) -> io::Result<usize> {
                 match io_core::synchronize(file) {
                     Err(error) => Err(error),
                     Ok(()) => io_core::write_once(file, bytes),
                 }
             }
             """,
             global: false
           ), "Properties"},
          {String.replace(rust, "append_record(&mut guard, value)", "Ok(true)"),
           "LockedProperties"},
          {String.replace(rust, "std::io::SeekFrom::End(0)", "std::io::SeekFrom::Start(0)"),
           "AppendProperties"},
          {String.replace(rust, "values.push(value)", "values.push(0)"), "AppendProperties"},
          {String.replace(
             rust,
             "Ok(None) => return Ok(values),",
             "Ok(None) => return Ok(Vec::new()),"
           ), "TailProperties"},
          {String.replace(rust, "Ok(()) => io_core::synchronize(file),", "Ok(()) => Ok(()),"),
           "ResizeProperties"},
          {String.replace(
             rust,
             "let valid_bytes = (values.len() as u64) * 4;",
             "let valid_bytes = (values.len() as u64) * 5;"
           ), "ResizeProperties"},
          {String.replace(rust, "if values.len() == max_records {", "if false {"),
           "ResizeProperties"}
        ] do
      refute broken == rust
      File.write!(source, broken)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      assert error.message =~ "Record/#{proof}.lean:"
      File.write!(source, rust)
    end

    core = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(core)

    broken =
      String.replace(
        original,
        "if value ^ inverse == u16::MAX {",
        "if value ^ inverse != u16::MAX {"
      )

    refute broken == original
    File.write!(core, broken)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Record/IntegrityProperties.lean:"
    File.write!(core, original)

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end

  @tag :tmp_dir
  test "rejects consuming a file mutex when native file destruction is unmodeled", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    assert_raise CompileError,
                 ~r/unsupported native drop payload|native destruction requires|structural drop erasure rejected/,
                 fn ->
                   Lynx.Rust.verify!(workspace, "io-protocol",
                     roots: ["io_protocol::locked_append", "io_protocol::consume_file_mutex"],
                     execution: :runtime,
                     files: :regular,
                     tools: @tools,
                     lean_project: project,
                     build_dir: Path.join(tmp, "build")
                   )
                 end
  end
end
