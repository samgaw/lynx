defmodule Lynx.Rustler.ConcurrentLogTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for concurrent durable-log proofs")

  @tag :tmp_dir
  test "checks acknowledged durable records under every modelled schedule", %{tmp_dir: tmp} do
    %{options: options, prepared: prepared, workspace: workspace, project: project} =
      Lynx.Rust.IoFixture.prepare_shared!(tmp, @tools, [
        "ConcurrentStorageProperties",
        "SharedRecoveryProperties",
        "ConcurrentRecoveryProperties"
      ])

    options =
      Keyword.update!(options, :required_properties, fn properties ->
        properties ++
          [
            "Record.SharedRecoveryProperties.constructed_log_recovery",
            "Record.ConcurrentRecoveryProperties.checked_recovery"
          ]
      end)

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "ConcurrentLogLaws.exs"))
    calibrate(prepared.library, beam, tmp)

    law_options = [
      native: {Lynx.Rustler, options},
      initial_environment: "Record.ConcurrentStorageProperties.initial",
      options: [maxHeartbeats: 64_000_000, maxRecDepth: 4096],
      debug_dir: Path.join(tmp, "debug")
    ]

    export = Path.join(tmp, "concurrent-durable-log.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert Enum.all?(reports, &(&1.status == :ok)), failures(reports)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    property = Path.join(project, "Record/ConcurrentStorageProperties.lean")
    original = File.read!(property)

    wrong =
      String.replace(
        original,
        "#[13, 0, 242, 255, 19, 0, 236, 255]",
        "#[14, 0, 241, 255, 19, 0, 236, 255]"
      )
      |> String.replace(
        "#[19, 0, 236, 255, 13, 0, 242, 255]",
        "#[19, 0, 236, 255, 14, 0, 241, 255]"
      )

    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property, original)

    # The Elixir program's incorrect expectation must fail at its own law, even
    # though all Rust implementations and recovery contracts still verify.
    source = Path.join(@fixture, "ConcurrentLogLaws.exs")
    law = File.read!(source)
    wrong_law = String.replace(law, "appended and peer", "not (appended and peer)")
    refute wrong_law == law
    [{_, wrong_beam}] = Code.compile_string(wrong_law, source)
    wrong_reports = Lynx.Laws.verify([wrong_beam], law_options)

    assert %{status: :error, diagnostics: diagnostics} =
             Enum.find(
               wrong_reports,
               &(&1.module == "Elixir.LynxIoFixture.ConcurrentLogLaws.laws")
             )

    assert Enum.any?(
             diagnostics,
             &match?(%{severity: :error, declaration: "concurrent_append/0"}, &1)
           )

    refute Enum.any?(diagnostics, &String.contains?(&1.message, "Unknown identifier"))
    Code.compile_string(law, source)

    for extra <- [
          "private axiom storageTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, original)
    # Replacing actual inode synchronization with success must invalidate the
    # implementation contracts rather than reusing a prior successful proof.
    core = Path.join(workspace, "core/src/lib.rs")
    implementation = File.read!(core)

    changed =
      String.replace(
        implementation,
        "pub fn synchronize(file: &File) -> io::Result<()> {\n    file.sync_all()\n}",
        "pub fn synchronize(_file: &File) -> io::Result<()> {\n    Ok(())\n}"
      )

    refute changed == implementation
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, implementation)
    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end

  defp failures(reports) do
    reports
    |> Enum.reject(&(&1.status == :ok))
    |> Enum.map(&Map.take(&1, [:module, :status, :diagnostics]))
    |> inspect(limit: :infinity)
  end

  defp calibrate(library, beam, tmp) do
    directory = Path.join(tmp, "live-log")
    File.mkdir_p!(directory)
    native = Path.join(directory, "native")
    File.cp!(library, native <> ".so")
    module = Path.join(directory, "Elixir.LynxIoFixture.ConcurrentLogLaws")
    File.write!(module <> ".beam", beam)
    script = Path.join(directory, "check.exs")

    File.write!(script, """
    Code.require_file(#{inspect(Path.join(@fixture, "NativeLogBindings.exs"))})
    {:module, LynxIoFixture.ConcurrentLogLaws} = :code.load_abs(~c"#{module}")
    :ok = LynxIoFixture.Native.load(~c"#{native}")
    true = LynxIoFixture.ConcurrentLogLaws.concurrent_append()
    contents = File.read!("journal")
    true = contents in [
      <<13::little-16, 65_522::little-16, 19::little-16, 65_516::little-16>>,
      <<19::little-16, 65_516::little-16, 13::little-16, 65_522::little-16>>
    ]
    """)

    {output, status} = System.cmd("elixir", [script], cd: directory, stderr_to_stdout: true)
    assert status == 0, output
  end
end
