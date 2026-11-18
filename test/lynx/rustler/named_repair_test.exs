defmodule Lynx.Rustler.NamedRepairTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000

  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "+owned-drops-v1"),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned runtime backend")

  @tag :tmp_dir
  test "verifies arbitrary named repair and the Rustler return boundary", %{tmp_dir: tmp} do
    extra =
      ~w(NamedJournalCrash NamedRepairAcknowledgement NamedRepairCrash NamedRustlerRepair NamedRustlerAdapterProof
      NamedRustlerLaw RecoveryScanInvariant RepairAcknowledgement RepairCrashProperties
      RepairImageInvariant RepairReturnProperties RepeatedRepairProperties)

    {workspace, project, fixture} = Lynx.Rust.IoFixture.prepare!(tmp, @tools, extra)

    modules =
      Enum.map(
        ~w(AppendProperties CrashProperties FileView IntegrityProperties LogProperties Properties
        ReadProperties RecoveryProperties ResizeProperties TailProperties) ++ extra,
        &("Record." <> &1)
      )

    Lynx.Rust.IoFixture.qualify_shared_proofs!(project, modules)

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      branching: :duplicate,
      cargo: [features: ["fallible-reopen"]],
      only: [log_try_reopen: 1],
      proof_roots: fixture[:roots],
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(options)

    assert [%{"name" => "log_try_reopen", "arity" => 1, "flags" => 2, "lean_name" => reopen}] =
             discovered.bindings.bindings

    for name <- ~w(NamedRepairCrash NamedRustlerRepair NamedRustlerAdapterProof NamedRustlerLaw) do
      path = Path.join(project, "Record/" <> name <> ".lean")
      File.write!(path, String.replace(File.read!(path), "__TRY_REOPEN__", reopen))
    end

    properties =
      ~w(Record.NamedRustlerRepair.arbitrary_repair_result
      Record.NamedRustlerRepair.arbitrary_repair_persists
      Record.NamedRepairCrash.typed_retry_after_prefix_crashes
      Record.NamedRustlerAdapterProof.arbitrary_repair_encodes
      Record.NamedRustlerLaw.concrete_raw_result)

    prefix_property = "Record.NamedRepairCrash.arbitrary_repair_prefix_crash"

    options =
      options ++ [proof_modules: modules, required_properties: [prefix_property | properties]]

    checked = Lynx.Rustler.prepare!(options)

    assert Enum.any?(checked.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract && evidence.theorem == prefix_property &&
               evidence.rust_name == "io_protocol::repair_log"
           end)

    for property <- properties do
      assert Enum.any?(checked.verification.guarantees, fn evidence ->
               evidence.kind == :cross_crate_contract && evidence.lean_name == reopen &&
                 evidence.theorem == property
             end)
    end

    path = Path.join(workspace, "protocol/src/lib.rs")
    source = File.read!(path)

    for {correct, wrong} <- [
          {"Ok(()) => io_core::synchronize(file)", "Ok(()) => Ok(())"},
          {"resize_then_sync(file, valid_bytes)", "resize_then_sync(file, 0)"}
        ] do
      assert [_] = :binary.matches(source, correct)

      try do
        File.write!(path, String.replace(source, correct, wrong))

        error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end

        assert error.message =~
                 ~r/(RepairAcknowledgement|ResizeProperties|RepairImageInvariant|RepairReturnProperties)\.lean:\d+:/

        refute error.message =~ ~r/Unknown (identifier|constant)/
      after
        File.write!(path, source)
      end
    end

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "NamedRustlerLaw.exs"))

    law_options = [
      native: {Lynx.Rustler, options},
      initial_environment: "Record.NamedRustlerLaw.repairBoot",
      options: [maxHeartbeats: 64_000_000, maxRecDepth: 8192]
    ]

    export = Path.join(tmp, "named-repair.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert Enum.any?(reports, &(&1.theorems != []))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok && &1.cached))

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
