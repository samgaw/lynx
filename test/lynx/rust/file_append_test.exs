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
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Record"))

    sources = [
      {"Properties", [{"Disk", "Record"}]},
      {"ReadProperties",
       [
         {"Read.Properties", "Record.Properties"},
         {"Read.ReadProperties", "Record.ReadProperties"}
       ]},
      {"RecoveryProperties",
       [
         {"Recovery.Properties", "Record.Properties"},
         {"Recovery.ReadProperties", "Record.ReadProperties"},
         {"Recovery.Extraction", "Record.Extraction"},
         {"Recovery.RecoveryProperties", "Record.RecoveryProperties"}
       ]},
      {"IntegrityProperties", []},
      {"CrashProperties", []},
      {"AppendProperties", []},
      {"LogProperties", []},
      {"TailProperties", []},
      {"ResizeProperties", []}
    ]

    for {module, replacements} <- sources do
      source = File.read!(Path.join(@fixture, module <> ".lean"))

      source =
        Enum.reduce(replacements, source, fn {old, new}, text ->
          String.replace(text, old, new)
        end)

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), source)
    end

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: [
        "io_protocol::resize_then_sync",
        "io_protocol::repair_log",
        "io_protocol::append_record",
        "io_protocol::recover_log",
        "io_protocol::recover_record",
        "io_protocol::write_record",
        "io_protocol::write_then_sync",
        "io_protocol::recover_word"
      ],
      execution: :runtime,
      files: :regular,
      tools: @tools,
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: Enum.map(sources, fn {name, _} -> "Record." <> name end),
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
          )
    ]

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

    for target <- [
          "Record/AppendProperties.lean",
          "Record/LogProperties.lean",
          "Record/TailProperties.lean",
          "Record/ResizeProperties.lean",
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

    source = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(source)

    for {broken, proof} <- [
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

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
