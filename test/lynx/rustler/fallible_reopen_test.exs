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
      only: [log_try_reopen: 1],
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "log_try_reopen",
               "arity" => 1,
               "flags" => 2,
               "lean_name" => implementation
             }
           ] =
             discovered.bindings.bindings

    proofs = [
      {"FallibleReopen", "errors_preserve_completed_records"},
      {"FallibleRetry", "reopens_after_typed_failure"},
      {"RepairIoFailures", "repair_failure_consumes_owners"}
    ]

    for {module, _} <- proofs do
      source = File.read!(Path.join(@fixture, module <> ".lean"))

      File.write!(
        Path.join(project, "Record/" <> module <> ".lean"),
        String.replace(source, "__TRY_REOPEN__", implementation)
      )
    end

    properties = for {module, name} <- proofs, do: "Record." <> module <> "." <> name

    options =
      Keyword.merge(options,
        proof_modules: for({module, _} <- proofs, do: "Record." <> module),
        required_properties: properties
      )

    prepared = Lynx.Rustler.prepare!(options)

    for property <- properties do
      assert Enum.any?(prepared.verification.guarantees, fn evidence ->
               evidence.kind == :cross_crate_contract && evidence.lean_name == implementation &&
                 evidence.theorem == property
             end)
    end

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))

    beams =
      for fixture <- ~w(FallibleReopenLaws FallibleRetryLaws),
          {module, beam} <- Code.compile_file(Path.join(@fixture, fixture <> ".exs")),
          into: %{},
          do: {module, beam}

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

    for {module, environment, boot} <- [
          {LynxIoFixture.RecordLimitLaws, "FallibleReopen", "limitedBoot"},
          {LynxIoFixture.JournalIoLaws, "FallibleReopen", "failedOpenBoot"},
          {LynxIoFixture.RecordLimitRetryLaws, "FallibleRetry", "limitedRetry"},
          {LynxIoFixture.JournalIoRetryLaws, "FallibleRetry", "failedOpenRetry"}
        ] do
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

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
    end

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
end
