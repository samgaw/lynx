defmodule Lynx.Rustler.RepairingLogTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_800_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "compiled repairing NIFs compose decoding, durable writes and recovery into Elixir laws",
       %{
         tmp_dir: tmp
       } do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, ~w(RepeatedRepairProperties
        RecoveryScanInvariant RepairReturnProperties RepairImageInvariant
        RepairAcknowledgement RepairWriterProperties AppendAcknowledgement
        RepairAppendAcknowledgement EncodedPrefixRecovery AppendPrefixInvariant
        RecoveryFrame RepairPrefixReturn RecoveryPrefixInvariant RepairPrefixInvariant
        RepairAppendPrefixInvariant FileReturnIdentity LockedPrefixInvariant))

    for module <- base[:proof_modules] do
      path = Path.join(project, String.replace(module, ".", "/") <> ".lean")

      source =
        File.read!(path)
        |> String.replace("Lynx io_protocol", "Lynx io_native io_native.io_protocol")
        |> String.replace("NativeDrop.drop", "NativeOwnedDrop.drop")

      File.write!(path, source)
    end

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      cargo: [features: ["shared-log"]],
      only: [log_repair_append: 3],
      proof_roots:
        base[:roots] ++
          ["io_protocol::repair_and_append", "io_protocol::locked_repair_and_append"],
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "log_repair_append",
               "arity" => 3,
               "flags" => 2,
               "arguments" => [
                 %{"resource" => ["io_native", "shared_log", "LogResource"]},
                 "u32",
                 "u16"
               ]
             } = binding
           ] =
             prepared.bindings.bindings

    source =
      File.read!(Path.join(@fixture, "RepairingLogProperties.lean"))
      |> String.replace("__REPAIR_APPEND__", binding["lean_name"])

    adapter_source =
      File.read!(Path.join(@fixture, "GuardedRepairAdapter.lean"))
      |> String.replace("__REPAIR_APPEND__", binding["lean_name"])

    adapter_property = Path.join(project, "Record/GuardedRepairAdapter.lean")
    File.write!(adapter_property, adapter_source)

    property = Path.join(project, "Record/RepairingLogProperties.lean")
    File.write!(property, source)

    properties =
      Enum.map(
        ~w(facade_contract critical_contract completed_checked limit_checked
      io_error_checked acknowledged_crash),
        &("Record.RepairingLogProperties." <> &1)
      )

    properties =
      properties ++
        Enum.map(
          ~w(locked_safe borrow_safe borrow_returns facade_safe adapter_safe),
          &("Record.GuardedRepairAdapter." <> &1)
        )

    options =
      options ++
        [
          proof_modules: ["Record.RepairingLogProperties", "Record.GuardedRepairAdapter"],
          required_properties: properties
        ]

    checked = Lynx.Rustler.prepare!(options)

    for theorem <- properties do
      assert Enum.any?(
               checked.verification.guarantees,
               &(&1.kind == :cross_crate_contract and &1.theorem == theorem)
             )
    end

    calibrate(prepared.library, tmp)
    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    laws = Code.compile_file(Path.join(@fixture, "RepairingLogLaws.exs"))

    for {module, beam} <- laws do
      initial =
        case module do
          LynxIoFixture.RepairingLimitLaws -> "limitInitial"
          LynxIoFixture.RepairingErrorLaws -> "errorInitial"
          _ -> "initial"
        end

      law_options = [
        native: {Lynx.Rustler, options},
        initial_environment: "Record.RepairingLogProperties." <> initial,
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      ]

      export = Path.join(tmp, Atom.to_string(module) <> ".export")
      reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
      assert Enum.all?(reports, &(&1.status == :ok)), failures(reports)
      guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

      for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
          do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

      assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
    end

    # An incorrect Elixir expectation must fail after the native proofs succeed.
    law_file = Path.join(@fixture, "RepairingLogLaws.exs")
    original_laws = File.read!(law_file)
    wrong = String.replace(original_laws, "resource, 4, 23)", "resource, 0, 23)")
    refute wrong == original_laws
    wrong_laws = Code.compile_string(wrong, law_file)

    {_, wrong_beam} =
      Enum.find(wrong_laws, fn {mod, _} -> mod == LynxIoFixture.RepairingLogLaws end)

    reports =
      Lynx.Laws.verify([wrong_beam],
        native: {Lynx.Rustler, options},
        initial_environment: "Record.RepairingLogProperties.initial",
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      )

    assert Enum.any?(reports, &(&1.status == :error)), inspect(reports)

    refute Enum.any?(reports, fn report ->
             Enum.any?(
               Map.get(report, :diagnostics, []),
               &String.contains?(&1.message, "Unknown identifier")
             )
           end)

    Code.compile_string(original_laws, law_file)

    for {correct, wrong} <- [
          {"[13#u16,19#u16,23#u16]", "[13#u16,19#u16,29#u16]"},
          {"(4,NativeIoError.typeName,.atom \"live\")",
           "(4,NativeIoError.typeName,.atom \"custom\")"}
        ] do
      broken = String.replace(source, correct, wrong)
      refute broken == source
      File.write!(property, broken)
      error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert error.message =~ "RepairingLogProperties.lean:"
      refute error.message =~ "Unknown identifier"
    end

    File.write!(property, source)

    # A false owner identity and a prefix claimed before it is appended both fail
    # against the extracted facade, including the actual resource decoder.
    for {correct, wrong} <- [
          {"owner = ⟨3,7⟩ ∧ world = decoded", "owner = ⟨3,8⟩ ∧ world = decoded"},
          {"Result.NativeInvariant (Safe values) (do",
           "Result.NativeInvariant (Safe (values ++ [value])) (do"}
        ] do
      broken = String.replace(adapter_source, correct, wrong)
      refute broken == adapter_source
      File.write!(adapter_property, broken)
      error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert error.message =~ "GuardedRepairAdapter.lean:"
      refute error.message =~ "Unknown identifier"
    end

    File.write!(adapter_property, adapter_source)

    for extra <- [
          "private axiom repairTrust : False",
          "private theorem unfinishedRepair : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")
      error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert error.message =~ "audit"
    end

    File.write!(property, source)

    for {relative, correct, wrong} <- [
          {"native/src/lib.rs", "repair_append(&resource, max_records as usize, value)",
           "repair_append(&resource, 0, value)"},
          {"protocol/src/lib.rs", "Ok(()) => io_core::synchronize(file)", "Ok(()) => Ok(())"}
        ] do
      path = Path.join(workspace, relative)
      original = File.read!(path)
      broken = String.replace(original, correct, wrong)
      refute broken == original
      File.write!(path, broken)
      error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert error.message =~ ~r/Record\/[^\s]+\.lean:\d+:/
      refute error.message =~ "Unknown identifier"
      File.write!(path, original)
      assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
    end
  end

  defp failures(reports), do: inspect(Enum.reject(reports, &(&1.status == :ok)), limit: :infinity)

  defp calibrate(library, tmp) do
    runtime = Path.join(tmp, "runtime")
    File.mkdir_p!(runtime)
    File.cp!(library, Path.join(runtime, "native.so"))
    path = Path.join(runtime, "check.exs")

    File.write!(path, """
    Code.compile_file(#{inspect(Path.join(@fixture, "NativeLogBindings.exs"))})
    :ok = LynxIoFixture.Native.load(String.to_charlist(#{inspect(Path.join(runtime, "native"))}))
    File.write!("journal", <<13,0,242,255,7>>)
    resource = LynxIoFixture.Native.log_reopen(4)
    File.write!("journal", <<13,0,242,255,7>>)
    false = LynxIoFixture.Native.log_repair_append(resource, 0, 19)
    <<13,0,242,255,7>> = File.read!("journal")
    for args <- [[resource, -1, 19], [resource, 4_294_967_296, 19],
                 [resource, 4, 4_294_967_296], [:wrong, 4, 19]] do
      :ok = try do
        apply(LynxIoFixture.Native, :log_repair_append, args)
        :unexpected
      catch :error, :badarg -> :ok end
    end
    <<13,0,242,255,7>> = File.read!("journal")
    true = LynxIoFixture.Native.log_repair_append(resource, 4, 19)
    true = LynxIoFixture.Native.log_repair_append(resource, 4, 23)
    <<13,0,242,255,19,0,236,255,23,0,232,255>> = File.read!("journal")
    """)

    {output, status} = System.cmd("elixir", [path], cd: runtime, stderr_to_stdout: true)
    assert status == 0, output
  end
end
