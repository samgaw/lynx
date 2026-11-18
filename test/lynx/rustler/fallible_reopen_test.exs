defmodule Lynx.Rustler.FallibleReopenTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000

  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "+owned-drops-v1"),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned runtime backend")

  @tag :tmp_dir
  test "verifies typed reopen failures and preserves completed records", %{tmp_dir: tmp} do
    {workspace, project, options, bindings} = prepare_reopen!(tmp)

    proofs = [
      {"FallibleReopen", "errors_preserve_completed_records"},
      {"FallibleRetry", "reopens_after_typed_failure"},
      {"RepairIoFailures", "repair_failure_consumes_owners"}
    ]

    options = install_proofs!(options, bindings, proofs)
    assert_linkage!(options, bindings.try_reopen)

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))

    beams =
      for fixture <- ~w(FallibleReopenLaws FallibleRetryLaws),
          {module, beam} <- Code.compile_file(Path.join(@fixture, fixture <> ".exs")),
          into: %{},
          do: {module, beam}

    verify_laws!(tmp, project, options, beams, [
      {LynxIoFixture.RecordLimitLaws, "FallibleReopen", "limitedBoot"},
      {LynxIoFixture.JournalIoLaws, "FallibleReopen", "failedOpenBoot"},
      {LynxIoFixture.RecordLimitRetryLaws, "FallibleRetry", "limitedRetry"},
      {LynxIoFixture.JournalIoRetryLaws, "FallibleRetry", "failedOpenRetry"}
    ])

    path = Path.join(workspace, "native/src/journal_reopen.rs")
    source = File.read!(path)
    wrong = String.replace(source, ~s|RaiseAtom("record_limit")|, ~s|RaiseAtom("journal_io")|)
    refute wrong == source

    try do
      File.write!(path, wrong)

      assert_raise RuntimeError, ~r/FallibleReopen\.lean:\d+:/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    after
      File.write!(path, source)
    end

    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end

  @tag :tmp_dir
  test "recovers the named journal after typed sync failure and crash", %{tmp_dir: tmp} do
    {workspace, project, options, bindings} = prepare_reopen!(tmp)

    proofs = [
      {"FallibleReopen", "errors_preserve_completed_records"},
      {"NamedJournalCrash", nil},
      {"TornSyncFailure", "failed_sync_preserves_acknowledgements"},
      {"TornSyncRecovery", "reopens_captured_image"},
      {"TornSyncRecovery", "failed_sync_crash_reopens"},
      {"TornSyncRecovery", "reboot_witness"},
      {"TornSyncChains", "repeated_failed_sync"},
      {"TornSyncChains", "reopens_after_failed_attempts"}
    ]

    options = install_proofs!(options, bindings, proofs)
    assert_linkage!(options, bindings.try_reopen)

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    beams = Map.new(Code.compile_file(Path.join(@fixture, "TornSyncLaws.exs")))

    verify_laws!(tmp, project, options, beams, [
      {LynxIoFixture.TornSyncFailureLaws, "TornSyncFailure", "failedSyncBoot"},
      {LynxIoFixture.TornSyncRestartLaws, "TornSyncRecovery", "retryBoot"}
    ])

    path = Path.join(workspace, "protocol/src/lib.rs")
    source = File.read!(path)

    wrong =
      String.replace(
        source,
        "(values.len() as u64).checked_mul(4)",
        "(values.len() as u64).checked_mul(3)"
      )

    refute wrong == source

    try do
      File.write!(path, wrong)

      assert_raise RuntimeError, ~r/TornSync(Failure|Recovery)\.lean:\d+:/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    after
      File.write!(path, source)
    end

    assert_linkage!(options, bindings.try_reopen)
  end

  @tag :tmp_dir
  test "continues a typed restarted journal and preserves the next crash image", %{tmp_dir: tmp} do
    {workspace, project, options, bindings} =
      prepare_reopen!(tmp, log_try_reopen: 1, log_append: 2)

    composition =
      ~w(typed_reopen_append crash_after_typed_append crash_after_repeated_failed_sync)

    proofs =
      [
        {"FallibleReopen", nil},
        {"NamedJournalCrash", nil},
        {"TornSyncFailure", "failed_sync_preserves_acknowledgements"},
        {"TornSyncRecovery", "reboot_witness"},
        {"TornSyncChains", "failed_attempt_witness"},
        {"TypedRestartAppend", "boot_after_failed_sync"}
      ] ++ Enum.map(composition, &{"TypedRestartAppend", &1})

    options = install_proofs!(options, bindings, proofs)
    prepared = assert_linkage!(options, bindings.try_reopen)

    for property <- composition do
      assert_linkage!(prepared, bindings.append, "Record.TypedRestartAppend." <> property)
    end

    path = Path.join(workspace, "protocol/src/lib.rs")
    source = File.read!(path)
    full_write = "Ok(4) => match io_core::synchronize(file)"
    wrong = String.replace(source, full_write, "Ok(3) => match io_core::synchronize(file)")
    refute wrong == source

    try do
      File.write!(path, wrong)

      assert_raise RuntimeError, ~r/TypedRestartAppend\.lean:\d+:/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    after
      File.write!(path, source)
    end

    assert_linkage!(options, bindings.try_reopen)

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    beams = Map.new(Code.compile_file(Path.join(@fixture, "TypedRestartAppendLaws.exs")))

    verify_laws!(tmp, project, options, beams, [
      {LynxIoFixture.TypedRestartCommitLaws, "TypedRestartAppend", "commitBoot"},
      {LynxIoFixture.TypedRestartRollbackLaws, "TypedRestartAppend", "rollbackBoot"}
    ])
  end

  @tag :tmp_dir
  test "recovers after a mixed-mask crash during typed repair", %{tmp_dir: tmp} do
    {_workspace, project, options, bindings} = prepare_reopen!(tmp)

    witness = [
      {"FallibleReopen", nil},
      {"NamedJournalCrash", nil},
      {"TornSyncFailure", nil},
      {"TornSyncRecovery", nil},
      {"MixedRepairScripts", nil},
      {"MixedRepairWitness", "restart_from_witness"}
    ]

    law_options = install_proofs!(options, bindings, witness)
    assert_linkage!(law_options, bindings.try_reopen)

    path = Path.join(project, "Record/MixedRepairWitness.lean")
    source = File.read!(path)
    wrong = String.replace(source, "[0,77]", "[99,77]")
    refute wrong == source

    try do
      File.write!(path, wrong)

      assert_raise RuntimeError, ~r/MixedRepairWitness\.lean:\d+:/, fn ->
        Lynx.Rust.Project.build!(project, ["Record.MixedRepairWitness"])
      end
    after
      File.write!(path, source)
    end

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    beams = Map.new(Code.compile_file(Path.join(@fixture, "MixedRepairRestartLaw.exs")))

    verify_laws!(tmp, project, law_options, beams, [
      {LynxIoFixture.MixedRepairRestartLaws, "MixedRepairWitness", "restartBoot"}
    ])

    proofs =
      witness ++
        [
          {"MixedRepairRecovery", "all_admitted_masks"},
          {"MixedRepairRecovery", "reopens_after_prefix_crash"}
        ]

    options = install_proofs!(options, bindings, proofs)
    prepared = assert_linkage!(options, bindings.try_reopen)

    audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "mixed-repair.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [audit], export: export)
    assert_export!(project, export)
  end

  @tag :tmp_dir
  test "continues a typed journal after repeated interrupted repairs", %{tmp_dir: tmp} do
    {_workspace, project, options, bindings} =
      prepare_reopen!(tmp, log_try_reopen: 1, log_append: 2)

    proofs = [
      {"FallibleReopen", nil},
      {"NamedJournalCrash", nil},
      {"TornSyncFailure", nil},
      {"TornSyncRecovery", nil},
      {"TornSyncChains", nil},
      {"MixedRepairScripts", nil},
      {"MixedRepairRecovery", nil},
      {"MixedRepairWitness", nil},
      {"MixedRepairChains", "repeated_prefix_crashes"},
      {"MixedRepairChains", "reopens_after_repeated_prefix_crashes"},
      {"MixedRepairIdempotence", "idempotent_completed_recovery"},
      {"MixedRepairIdempotence", "mixed_then_completed"},
      {"MixedRepairChains", "interrupted_preserves"},
      {"MixedRepairAlternating", "alternating_repairs"},
      {"TypedRestartAppend", nil},
      {"MixedRepairAppend", "appends_after_mixed_interruptions"},
      {"MixedRepairAppend", "boot_after_two_interruptions"}
    ]

    options = install_proofs!(options, bindings, proofs)
    prepared = assert_linkage!(options, bindings.try_reopen)

    assert_linkage!(
      prepared,
      bindings.append,
      "Record.MixedRepairAppend.appends_after_mixed_interruptions"
    )

    path = Path.join(project, "Record/MixedRepairAppend.lean")
    source = File.read!(path)
    wrong = String.replace(source, "after.highWater + 8", "after.highWater + 7")
    refute wrong == source

    try do
      File.write!(path, wrong)

      assert_raise RuntimeError, ~r/MixedRepairAppend\.lean:\d+:/, fn ->
        Lynx.Rust.Project.build!(project, ["Record.MixedRepairAppend"])
      end
    after
      File.write!(path, source)
    end

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    beams = Map.new(Code.compile_file(Path.join(@fixture, "MixedRepairAppendLaw.exs")))

    verify_laws!(tmp, project, options, beams, [
      {LynxIoFixture.MixedRepairAppendLaws, "MixedRepairAppend", "commitBoot"}
    ])
  end

  defp prepare_reopen!(tmp, only \\ [log_try_reopen: 1]) do
    {workspace, project, _fixture} = Lynx.Rust.IoFixture.prepare!(tmp, @tools)

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      branching: :duplicate,
      cargo: [features: ["fallible-reopen"]],
      only: only,
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(options)

    bindings =
      for binding <- discovered.bindings.bindings, into: %{} do
        assert %{"name" => name, "arity" => arity, "flags" => 2, "lean_name" => target} = binding
        {{name, arity}, target}
      end

    assert Enum.sort(Map.keys(bindings)) ==
             Enum.sort(for {name, arity} <- only, do: {Atom.to_string(name), arity})

    {workspace, project, options,
     %{
       try_reopen: Map.fetch!(bindings, {"log_try_reopen", 1}),
       append: bindings[{"log_append", 2}]
     }}
  end

  defp install_proofs!(options, bindings, proofs) do
    project = Keyword.fetch!(options, :lean_project)
    modules = proofs |> Enum.map(&elem(&1, 0)) |> Enum.uniq()

    for module <- modules do
      source = File.read!(Path.join(@fixture, module <> ".lean"))

      source = String.replace(source, "__TRY_REOPEN__", bindings.try_reopen)

      source =
        if bindings.append,
          do: String.replace(source, "__APPEND__", bindings.append),
          else: source

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), source)
    end

    Keyword.merge(options,
      proof_modules: Enum.map(modules, &("Record." <> &1)),
      required_properties:
        for({module, name} <- proofs, name != nil, do: "Record." <> module <> "." <> name)
    )
  end

  defp assert_linkage!(options, implementation) do
    prepared = Lynx.Rustler.prepare!(options)

    for property <- Keyword.fetch!(options, :required_properties) do
      assert_linkage!(prepared, implementation, property)
    end

    prepared
  end

  defp assert_linkage!(prepared, implementation, property) do
    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract && evidence.lean_name == implementation &&
               evidence.theorem == property
           end)
  end

  defp verify_laws!(tmp, project, options, beams, cases) do
    for {module, environment, boot} <- cases do
      beam = Map.fetch!(beams, module)
      export = Path.join(tmp, boot <> ".export")

      law_options = [
        native: {Lynx.Rustler, options},
        initial_environment: "Record." <> environment <> "." <> boot,
        options: [maxHeartbeats: 32_000_000, maxRecDepth: 8192]
      ]

      reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
      assert Enum.any?(reports, &(&1.theorems != []))
      assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
      assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

      assert_export!(project, export)
    end
  end

  defp assert_export!(project, export) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
