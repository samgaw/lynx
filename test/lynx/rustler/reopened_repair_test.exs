defmodule Lynx.Rustler.ReopenedRepairTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000

  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(
             File.read!(Path.join(@tools, "lynx-toolchain")),
             "partial-discriminants-v1"
           ),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the partial-discriminants backend")

  @tag :tmp_dir
  test "recovers the named Rustler log after any finite sequence of admitted repair crashes",
       %{tmp_dir: tmp} do
    properties =
      Enum.map(
        ~w(blocked_sync_checked restart_prefixes_checked named_retry_checked
        retry_after_crashes blocked_reboot_witness),
        &("Record.ReopenedRepairPrefix." <> &1)
      ) ++
        Enum.map(
          ~w(retry_complete_log blocked_complete complete_attempts_witness complete_boot_reachable),
          &("Record.CompleteNamedRepair." <> &1)
        )

    {options, workspace, project, reopen, _append} = prepare_reopen!(tmp, [], properties)
    prepared = Lynx.Rustler.prepare!(options)

    for property <- properties do
      assert Enum.any?(prepared.verification.guarantees, fn guarantee ->
               guarantee.kind == :cross_crate_contract &&
                 guarantee.lean_name == reopen["lean_name"] &&
                 guarantee.theorem == property
             end)
    end

    calibrate(prepared.library, tmp)
    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

    for {mod, boot, export_name} <- [
          {"ReopenedRepairLaws", "Record.ReopenedRepairPrefix.recoveredBoot",
           "repaired-after-reboot.export"},
          {"CompleteNamedRepairLaws", "Record.CompleteNamedRepair.completeBoot",
           "complete-after-reboot.export"}
        ] do
      [{_, beam}] = Code.compile_file(Path.join(@fixture, mod <> ".exs"))

      law_options = [
        native: {Lynx.Rustler, options},
        initial_environment: boot,
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      ]

      export = Path.join(tmp, export_name)
      reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
      assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
      assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
    end

    complete_proof = Path.join(project, "Record/CompleteNamedRepair.lean")
    complete_source = File.read!(complete_proof)

    wrong =
      String.replace(
        complete_source,
        "file.position == bytes.size &&",
        "file.position == bytes.size + 1 &&"
      )

    refute wrong == complete_source

    try do
      File.write!(complete_proof, wrong)

      assert_raise RuntimeError, ~r/CompleteNamedRepair\.lean:/, fn ->
        Lynx.Rust.Project.build!(project, ["Record.CompleteNamedRepair"])
      end
    after
      File.write!(complete_proof, complete_source)
    end

    proof = Path.join(project, "Record/ReopenedRepairPrefix.lean")
    original = File.read!(proof)
    wrong = String.replace(original, "file.position == eof &&", "file.position == eof + 1 &&")
    refute wrong == original
    File.write!(proof, wrong)

    assert_raise RuntimeError, ~r/ReopenedRepairPrefix\.lean:/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(proof, original)

    protocol = Path.join(workspace, "protocol/src/lib.rs")
    implementation = File.read!(protocol)

    unsynchronized =
      String.replace(implementation, "Ok(()) => io_core::synchronize(file),", "Ok(()) => Ok(()),")

    refute unsynchronized == implementation
    File.write!(protocol, unsynchronized)

    assert_raise RuntimeError, ~r/\.lean:/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(protocol, implementation)
    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end

  @tag :tmp_dir
  test "commits or rolls back through a writable resource reopened after a crash", %{tmp_dir: tmp} do
    properties =
      for name <- ~w(append_after_repeated_reopen resume_boot_reachable),
          do: "Record.CompleteReopenAppend." <> name

    {options, _workspace, project, reopen, append} =
      prepare_reopen!(tmp, ["CompleteReopenAppend"], properties)

    prepared = Lynx.Rustler.prepare!(options)

    for implementation <- [reopen, append] do
      assert Enum.any?(prepared.verification.guarantees, fn guarantee ->
               guarantee.kind == :cross_crate_contract &&
                 guarantee.lean_name == implementation["lean_name"] &&
                 guarantee.theorem == "Record.CompleteReopenAppend.append_after_repeated_reopen"
             end)
    end

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    beams = Map.new(Code.compile_file(Path.join(@fixture, "CompleteReopenAppendLaws.exs")))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

    for {module, boot, name} <- [
          {LynxIoFixture.CompleteReopenCommitLaws, "commitBoot", "commit"},
          {LynxIoFixture.CompleteReopenRollbackLaws, "rollbackBoot", "rollback"}
        ] do
      beam = Map.fetch!(beams, module)

      law_options = [
        native: {Lynx.Rustler, options},
        initial_environment: "Record.CompleteReopenAppend." <> boot,
        options: [maxHeartbeats: 32_000_000, maxRecDepth: 8192]
      ]

      export = Path.join(tmp, name <> "-after-reopen.export")
      reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
      assert Enum.any?(reports, &(&1.theorems != []))
      assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
      assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
    end

    proof = Path.join(project, "Record/CompleteReopenAppend.lean")
    source = File.read!(proof)
    wrong = String.replace(source, "handle.inode == 1", "handle.inode == 2")
    refute wrong == source

    try do
      File.write!(proof, wrong)

      assert_raise RuntimeError, ~r/CompleteReopenAppend\.lean:/, fn ->
        Lynx.Rust.Project.build!(project, ["Record.CompleteReopenAppend"])
      end
    after
      File.write!(proof, source)
    end
  end

  defp prepare_reopen!(tmp, extra_modules, properties) do
    modules =
      ~w(ReopenedLogProperties ReopenedRepairPrefix RepeatedRepairProperties CompleteNamedRepair) ++
        extra_modules

    %{options: options, workspace: workspace, project: project} =
      Lynx.Rust.IoFixture.prepare_shared!(tmp, @tools, ["SharedRecoveryProperties"])

    options = Keyword.put(options, :only, log_create: 0, log_append: 2, log_reopen: 1)

    prepared =
      Lynx.Rustler.prepare!(Keyword.drop(options, [:proof_modules, :required_properties]))

    reopen = Enum.find(prepared.bindings.bindings, &(&1["name"] == "log_reopen"))
    append = Enum.find(prepared.bindings.bindings, &(&1["name"] == "log_append"))
    assert %{"arity" => 1, "flags" => 2} = reopen

    for module <- modules do
      source =
        File.read!(Path.join(@fixture, module <> ".lean"))
        |> String.replace("__REOPEN__", reopen["lean_name"])
        |> String.replace("__APPEND__", append["lean_name"])
        |> String.replace("Lynx io_protocol", "Lynx io_native io_native.io_protocol")

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), source)
    end

    options =
      options
      |> Keyword.update!(
        :proof_modules,
        &(&1 ++ Enum.map(modules, fn module -> "Record." <> module end))
      )
      |> Keyword.update!(:required_properties, &(&1 ++ properties))

    {options, workspace, project, reopen, append}
  end

  defp calibrate(library, tmp) do
    runtime = Path.join(tmp, "reboot")
    File.mkdir_p!(runtime)
    File.cp!(library, Path.join(runtime, "native.so"))

    path = Path.join(runtime, "check.exs")

    File.write!(path, """
    Code.require_file(#{inspect(Path.join(@fixture, "NativeLogBindings.exs"))})
    :ok = LynxIoFixture.Native.load(~c"./native")
    File.write!("journal", <<13, 0, 242, 255, 99, 0>>)
    true = is_reference(LynxIoFixture.Native.log_reopen(2))
    <<13, 0, 242, 255>> = File.read!("journal")
    """)

    {output, status} = System.cmd("elixir", [path], cd: runtime, stderr_to_stdout: true)
    assert status == 0, output
  end
end
