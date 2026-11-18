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
    %{options: options, workspace: workspace, project: project} =
      Lynx.Rust.IoFixture.prepare_shared!(tmp, @tools, ["SharedRecoveryProperties"])

    options = Keyword.put(options, :only, log_create: 0, log_append: 2, log_reopen: 1)

    prepared =
      Lynx.Rustler.prepare!(Keyword.drop(options, [:proof_modules, :required_properties]))

    reopen = Enum.find(prepared.bindings.bindings, &(&1["name"] == "log_reopen"))
    append = Enum.find(prepared.bindings.bindings, &(&1["name"] == "log_append"))
    assert %{"arity" => 1, "flags" => 2} = reopen

    for module <- ~w(ReopenedLogProperties ReopenedRepairPrefix RepeatedRepairProperties) do
      source =
        File.read!(Path.join(@fixture, module <> ".lean"))
        |> String.replace("__REOPEN__", reopen["lean_name"])
        |> String.replace("__APPEND__", append["lean_name"])
        |> String.replace("Lynx io_protocol", "Lynx io_native io_native.io_protocol")

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), source)
    end

    properties =
      Enum.map(
        ~w(blocked_sync_checked restart_prefixes_checked named_retry_checked
        retry_after_crashes blocked_reboot_witness),
        &("Record.ReopenedRepairPrefix." <> &1)
      )

    options =
      options
      |> Keyword.update!(
        :proof_modules,
        &(&1 ++
            ~w(Record.ReopenedLogProperties Record.RepeatedRepairProperties Record.ReopenedRepairPrefix))
      )
      |> Keyword.update!(:required_properties, &(&1 ++ properties))

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
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "ReopenedRepairLaws.exs"))

    law_options = [
      native: {Lynx.Rustler, options},
      initial_environment: "Record.ReopenedRepairPrefix.recoveredBoot",
      options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
    ]

    export = Path.join(tmp, "repaired-after-reboot.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

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
