defmodule Lynx.Rustler.ConcurrentRollbackTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000

  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(
             File.read!(Path.join(@tools, "lynx-toolchain")),
             "+owned-drops-v1"
           ),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned runtime backend")

  @tag :tmp_dir
  test "serializes concurrent Rustler append and rollback and recovers their durable log",
       %{tmp_dir: tmp} do
    %{options: options, project: project, workspace: workspace} =
      Lynx.Rust.IoFixture.prepare_shared!(tmp, @tools, ["SharedRecoveryProperties"])

    options = Keyword.put(options, :only, log_create: 0, log_append: 2, log_reopen: 1)

    prepared =
      Lynx.Rustler.prepare!(Keyword.drop(options, [:proof_modules, :required_properties]))

    reopen = Enum.find(prepared.bindings.bindings, &(&1["name"] == "log_reopen"))
    append = Enum.find(prepared.bindings.bindings, &(&1["name"] == "log_append"))
    assert %{"arity" => 1, "flags" => 2} = reopen
    assert %{"arity" => 2, "flags" => 2} = append

    modules =
      ~w(ReopenedLogProperties ReopenedRepairPrefix RepeatedRepairProperties
      EncodedPrefixRecovery ConcurrentRollback SerialRepair)

    for module <- modules do
      source =
        File.read!(Path.join(@fixture, module <> ".lean"))
        |> String.replace("__REOPEN__", reopen["lean_name"])
        |> String.replace("__APPEND__", append["lean_name"])
        |> String.replace("Lynx io_protocol", "Lynx io_native io_native.io_protocol")
        |> String.replace("NativeDrop.drop", "NativeOwnedDrop.drop")

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), source)
    end

    properties =
      Enum.map(
        ~w(reopening_supplies_resource prefixes_checked all_prefixes_safe recover_observed
        terminal_serializes recover_serial_log),
        &("Record.ConcurrentRollback." <> &1)
      ) ++ ["Record.SerialRepair.retry_serial_log"]

    options =
      options
      |> Keyword.update!(
        :proof_modules,
        &(&1 ++ Enum.map(modules, fn module -> "Record." <> module end))
      )
      |> Keyword.update!(:required_properties, &(&1 ++ properties))

    prepared = Lynx.Rustler.prepare!(options)

    for {theorem, implementation} <- [
          {"reopening_supplies_resource", reopen["lean_name"]},
          {"prefixes_checked", append["lean_name"]},
          {"recover_observed", append["lean_name"]},
          {"recover_observed", "io_native.io_protocol.recover_log"},
          {"terminal_serializes", append["lean_name"]},
          {"recover_serial_log", "io_native.io_protocol.recover_log"}
        ] do
      assert Enum.any?(prepared.verification.guarantees, fn evidence ->
               evidence.kind == :rust_implementation and evidence.lean_name == implementation and
                 evidence.theorem == "Record.ConcurrentRollback." <> theorem
             end)
    end

    for implementation <- [append["lean_name"], "io_native.io_protocol.repair_log"] do
      assert Enum.any?(prepared.verification.guarantees, fn evidence ->
               evidence.kind == :rust_implementation and evidence.lean_name == implementation and
                 evidence.theorem == "Record.SerialRepair.retry_serial_log"
             end)
    end

    specification = Path.join(project, "Record/ConcurrentRollback.lean")
    source = File.read!(specification)

    swapped_replies =
      String.replace(
        source,
        "if leftFirst then ⟨log, firstReply, secondReply⟩ else ⟨log, secondReply, firstReply⟩",
        "if leftFirst then ⟨log, secondReply, firstReply⟩ else ⟨log, firstReply, secondReply⟩"
      )

    refute swapped_replies == source

    try do
      File.write!(specification, swapped_replies)

      assert_raise RuntimeError, ~r/prefix invariant rejected at a reachable configuration/, fn ->
        Lynx.Rust.Project.build!(project, ["Record.ConcurrentRollback"])
      end
    after
      File.write!(specification, source)
    end

    core = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(core)

    unsynchronized =
      String.replace(
        original,
        "pub fn synchronize(file: &File) -> io::Result<()> {\n    file.sync_all()",
        "pub fn synchronize(_file: &File) -> io::Result<()> {\n    Ok(())"
      )

    refute unsynchronized == original

    try do
      File.write!(core, unsynchronized)

      error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert error.message =~ ~r/Record\/[^\s]+\.lean:\d+:/
      refute error.message =~ "Unknown identifier"
    after
      File.write!(core, original)
    end

    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "ConcurrentRollbackLaws.exs"))

    law_options = [
      native: {Lynx.Rustler, options},
      initial_environment: "Record.ConcurrentRollback.afterReopen",
      options: [maxHeartbeats: 128_000_000, maxRecDepth: 8192]
    ]

    export = Path.join(tmp, "concurrent-rollback.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
