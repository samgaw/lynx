defmodule Lynx.Rustler.ReopenedLogTest do
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
  test "repairs a torn log and returns a verified shared Rustler resource", %{tmp_dir: tmp} do
    %{options: options, workspace: workspace, project: project} =
      Lynx.Rust.IoFixture.prepare_shared!(tmp, @tools)

    options = Keyword.put(options, :only, log_create: 0, log_append: 2, log_reopen: 1)

    prepared =
      Lynx.Rustler.prepare!(Keyword.drop(options, [:proof_modules, :required_properties]))

    binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == "log_reopen"))
    assert %{"arity" => 1, "flags" => 2} = binding
    property = Path.join(project, "Record/ReopenedLogProperties.lean")

    source =
      File.read!(Path.join(@fixture, "ReopenedLogProperties.lean"))
      |> String.replace("__REOPEN__", binding["lean_name"])

    File.write!(property, source)

    options =
      options
      |> Keyword.update!(:proof_modules, &(&1 ++ ["Record.ReopenedLogProperties"]))
      |> Keyword.update!(
        :required_properties,
        &(&1 ++ ["Record.ReopenedLogProperties.reopened_checked"])
      )

    prepared = Lynx.Rustler.prepare!(options)

    assert Enum.any?(
             prepared.verification.guarantees,
             &(Map.get(&1, :theorem) == "Record.ReopenedLogProperties.reopened_checked")
           )

    calibrate(prepared.library, tmp)
    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "ReopenedLogLaws.exs"))

    law_options = [
      native: {Lynx.Rustler, options},
      initial_environment: "Record.ReopenedLogProperties.initial",
      options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
    ]

    export = Path.join(tmp, "reopened-log.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(
             for report <- reports,
                 report.status != :ok,
                 do: Map.take(report, [:module, :diagnostics])
           )

    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom reopenTrust : False",
          "private theorem unfinishedReopen : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")
      error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert error.message =~ "audit"
    end

    File.write!(property, source)

    protocol = Path.join(workspace, "protocol/src/lib.rs")
    protocol_source = File.read!(protocol)

    unsynchronized =
      String.replace(
        protocol_source,
        "Ok(()) => io_core::synchronize(file),",
        "Ok(()) => Ok(()),"
      )

    refute unsynchronized == protocol_source
    File.write!(protocol, unsynchronized)
    error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    assert error.message =~ ".lean:"
    File.write!(protocol, protocol_source)

    native = Path.join(workspace, "native/src/lib.rs")
    original = File.read!(native)
    changed = String.replace(original, "reopen(max_records as usize)", "reopen(0)")
    refute changed == original
    File.write!(native, changed)
    error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    assert error.message =~ "ReopenedLogProperties.lean:"
    File.write!(native, original)
    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end

  defp calibrate(library, tmp) do
    runtime = Path.join(tmp, "runtime")
    File.mkdir_p!(runtime)
    File.cp!(library, Path.join(runtime, "native.so"))

    script = """
    Code.compile_file(#{inspect(Path.join(@fixture, "NativeLogBindings.exs"))})
    :ok = LynxIoFixture.Native.load(String.to_charlist(#{inspect(Path.join(runtime, "native"))}))
    File.write!("journal", <<13,0,242,255,99,0>>)
    resource = LynxIoFixture.Native.log_reopen(2)
    true = is_reference(resource)
    true = LynxIoFixture.Native.log_append(resource, 19)
    expected = <<13,0,242,255,19,0,236,255>>
    ^expected = File.read!("journal")
    for input <- [-1, 4_294_967_296, :wrong] do
      :ok = try do
        LynxIoFixture.Native.log_reopen(input)
        :unexpected
      catch :error, :badarg -> :ok end
    end
    :ok = try do
      LynxIoFixture.Native.log_reopen(1)
      :unexpected
    catch :error, :nif_panicked -> :ok end
    ^expected = File.read!("journal")
    """

    path = Path.join(runtime, "check.exs")
    File.write!(path, script)
    {output, status} = System.cmd("elixir", [path], cd: runtime, stderr_to_stdout: true)
    assert status == 0, output
  end
end
