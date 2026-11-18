defmodule Lynx.Rustler.PositionalIoTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "+owned-drops-v1"),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-drops backend")

  @proof_sources [
    {"Properties.lean", "Base"},
    {"PositionalProperties.lean", "Properties"},
    {"PositionalNifProperties.lean", "Nif"},
    {"PositionalOpenedProperties.lean", "Opened"}
  ]

  @tag :tmp_dir
  test "compiled positional calls preserve resource ownership and share the named inode",
       %{
         tmp_dir: tmp
       } do
    base = fixture!(tmp)
    workspace = base[:workspace]
    project = base[:lean_project]
    prepared = Lynx.Rustler.prepare!(base)
    bindings = Map.new(prepared.bindings.bindings, &{&1["name"], &1})

    resource = ["io_native", "offset_file", "OffsetFile"]

    assert %{
             "open_slots" => %{
               "flags" => 2,
               "arity" => 0,
               "rust_name" => "open_nif",
               "arguments" => [],
               "result" => %{"nif_result" => %{"resource" => ^resource}}
             },
             "patch_at" => %{
               "flags" => 2,
               "arity" => 3,
               "rust_name" => "patch_nif",
               "arguments" => [%{"resource" => ^resource}, "u64", "u8"],
               "result" => "bool"
             },
             "observe_at" => %{
               "flags" => 2,
               "arity" => 2,
               "rust_name" => "observe_nif",
               "arguments" => [%{"resource" => ^resource}, "u64"],
               "result" => %{"option" => "u8"}
             }
           } = bindings

    assert %{
             status: :validated_configuration,
             types: [%{rust_name: "io_native::offset_file::OffsetFile"}]
           } = prepared.resource_registration

    write_proofs!(project, bindings, @proof_sources)

    options =
      base ++
        [
          proof_modules:
            ~w(Positional.Base Positional.Properties Positional.Nif Positional.Opened),
          required_properties:
            ~w(Positional.Proofs.patch_persists_prefix Positional.Proofs.observe_prefix
          Positional.Proofs.observe_eof Positional.Nif.completed_program
          Positional.Opened.opened_shared_inode Positional.Opened.failed_open_releases_error)
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))

    assert Enum.any?(checked.verification.guarantees, fn
             %{
               kind: :cross_crate_contract,
               theorem: "Positional.Opened.opened_shared_inode",
               implementation_dependencies: dependencies
             } ->
               Enum.any?(dependencies, &(&1["rust_name"] == "io_protocol::open_readwrite"))

             _ ->
               false
           end)

    for operation <- ~w(open write_at read_at sync_data) do
      assert Enum.any?(
               checked.verification.unverified_external_calls,
               &String.ends_with?(&1.rust_name, "::" <> operation)
             )
    end

    for {name, arity} <- [{"open_slots", 0}, {"patch_at", 3}, {"observe_at", 2}] do
      assert Enum.any?(
               checked.verification.guarantees,
               &match?(
                 %{kind: :nif_adapter, function: ^name, arity: ^arity, status: :verified},
                 &1
               )
             )
    end

    refute Enum.any?(checked.verification.unverified_nif_exports, &(&1.function == "open_slots"))

    load_and_calibrate(prepared, tmp)

    beams = Map.new(Code.compile_file(Path.join(@fixture, "positional_laws.ex")))
    export = Path.join(tmp, "positional-nif.export")

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
    ]

    short_options = Keyword.put(law_options, :initial_environment, "Positional.Nif.short")

    for {module, environment, theorem} <- [
          {LynxPositionalFixture.Opened, "Positional.Opened.ready", "shared_inode/0"},
          {LynxPositionalFixture.Missing, "Positional.Opened.missing", "raises_open_failed/0"},
          {LynxPositionalFixture.Success, "Positional.Nif.ready", "patch_and_observe/0"},
          {LynxPositionalFixture.Short, "Positional.Nif.short", "zero_write_is_unacknowledged/0"},
          {LynxPositionalFixture.Invalid, "Positional.Nif.ready", "rejects_negative_offset/0"}
        ] do
      run_options = Keyword.put(law_options, :initial_environment, environment)

      run_options =
        if module == LynxPositionalFixture.Opened,
          do: Keyword.put(run_options, :export, export),
          else: run_options

      reports = Lynx.Laws.verify([Map.fetch!(beams, module)], run_options)

      assert [] ==
               for(
                 report <- reports,
                 report.status != :ok,
                 do: {report.module, report.diagnostics}
               )

      assert [%{name: ^theorem}] = Enum.flat_map(reports, & &1.theorems)
    end

    assert Enum.all?(
             Lynx.Laws.verify([beams[LynxPositionalFixture.Short]], short_options),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    property = Path.join(project, "Positional/Nif.lean")
    original = File.read!(property)

    for extra <- [
          "private axiom positionalTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, original)

    source = Path.join(workspace, "native/src/offset_file.rs")
    rust = File.read!(source)
    mutation = String.replace(rust, "Ok(count) => count == 1", "Ok(count) => count <= 1")
    refute mutation == rust
    File.write!(source, mutation)

    assert Enum.any?(
             Lynx.Laws.verify([beams[LynxPositionalFixture.Short]], short_options),
             fn report ->
               report.status == :error and
                 Enum.any?(
                   report.diagnostics,
                   &(&1[:declaration] == "zero_write_is_unacknowledged/0")
                 )
             end
           )

    File.write!(source, rust)

    mutation = String.replace(rust, ~s|RaiseAtom("open_failed")|, ~s|RaiseAtom("wrong_error")|)
    refute mutation == rust
    File.write!(source, mutation)

    error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    assert error.message =~ "Opened.lean:"
    assert error.message =~ "postcondition"
    File.write!(source, rust)
  end

  @tag :tmp_dir
  test "two compiled positional writers preserve a serial image across modeled interleavings", %{
    tmp_dir: tmp
  } do
    base = fixture!(tmp)
    project = base[:lean_project]
    prepared = Lynx.Rustler.prepare!(base)
    bindings = Map.new(prepared.bindings.bindings, &{&1["name"], &1})
    sources = @proof_sources ++ [{"PositionalConcurrentProperties.lean", "Concurrent"}]
    write_proofs!(project, bindings, sources)

    properties =
      Enum.map(
        ~w(patches_agree_with_serial_image peer_byte_reachable writer_byte_reachable),
        &("Positional.Concurrent." <> &1)
      )

    options =
      base ++
        [
          proof_modules: Enum.map(sources, fn {_, module} -> "Positional." <> module end),
          required_properties: properties
        ]

    load_and_calibrate(prepared, tmp)

    [{_, beam}] = Code.compile_file(Path.join(@fixture, "positional_concurrent_laws.ex"))
    export = Path.join(tmp, "concurrent-positional.export")

    law_options = [
      native: {Lynx.Rustler, options},
      initial_environment: "Positional.Concurrent.ready",
      options: [maxHeartbeats: 64_000_000, maxRecDepth: 8192]
    ]

    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

    assert [%{name: "concurrent_patches/0"}] = Enum.flat_map(reports, & &1.theorems)

    assert Enum.all?(
             Lynx.Laws.verify([beam], law_options),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(base[:workspace], "native/src/offset_file.rs")
    rust = File.read!(source)

    mutation =
      String.replace(
        rust,
        "    let reply = io_protocol::positional::patch",
        "    let offset = if offset == 0 { 1 } else { offset };\n" <>
          "    let reply = io_protocol::positional::patch"
      )

    refute mutation == rust
    File.write!(source, mutation)

    error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    assert error.message =~ "Positional/Concurrent.lean:"
    assert error.message =~ "postcondition rejected at a terminal configuration"
    File.write!(source, rust)
  end

  @tag :tmp_dir
  @tag timeout: 1_800_000
  test "admitted positional crashes and interrupted Rustler reopens preserve the named image", %{
    tmp_dir: tmp
  } do
    base = fixture!(tmp)
    project = base[:lean_project]
    prepared = Lynx.Rustler.prepare!(base)
    bindings = Map.new(prepared.bindings.bindings, &{&1["name"], &1})

    sources =
      @proof_sources ++
        [
          {"PositionalConcurrentProperties.lean", "Concurrent"},
          {"PositionalCrashProperties.lean", "Crash"},
          {"PositionalNamedRestartProperties.lean", "NamedRestart"}
        ]

    write_proofs!(project, bindings, sources)

    implementation_counts = %{
      "Positional.CrashPrefix.crashes_preserve_positional_bytes" => 2,
      "Positional.CrashRead.observes_after_restart" => 1,
      "Positional.CrashRecovery.crashes_recover_positional_byte" => 3,
      "Positional.NamedRestart.named_restart_reads" => 2,
      "Positional.NamedPrefix.retains_named_inode" => 2,
      "Positional.NamedCapture.named_crash_reopens" => 3,
      "Positional.Reopening.reopen_prefix_checked" => 2,
      "Positional.RepeatedReopen.crash_during_reopen" => 2,
      "Positional.RepeatedReopen.every_finite_reopen" => 2,
      "Positional.RepeatedReopen.named_crash_reopens_after_retries" => 3
    }

    proof_modules = Enum.map(sources, fn {_, module} -> "Positional." <> module end)
    required = Map.keys(implementation_counts)

    options = base ++ [proof_modules: proof_modules, required_properties: required]
    load_and_calibrate(prepared, tmp)

    [{_, beam}] = Code.compile_file(Path.join(@fixture, "positional_restarted_laws.ex"))
    export = Path.join(tmp, "positional-crash.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        initial_environment: "Positional.NamedRestart.afterSeven",
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192],
        export: export
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    assert [%{name: "reads_reopened_byte/0"}] = Enum.flat_map(reports, & &1.theorems)

    properties = Lynx.Rust.Proofs.properties!(reports)

    reported =
      properties
      |> Map.new(&{&1["theorem"], length(&1["implementations"])})
      |> Map.take(required)

    assert reported == implementation_counts

    facade_roots = MapSet.new(bindings, fn {_, binding} -> binding["lean_name"] end)

    for theorem <-
          ~w(Positional.NamedCapture.named_crash_reopens Positional.RepeatedReopen.named_crash_reopens_after_retries) do
      assert [%{"implementations" => roots}] =
               Enum.filter(properties, &(&1["theorem"] == theorem))

      assert MapSet.new(roots) == facade_roots
    end

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end

  defp fixture!(tmp) do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    facade = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      facade,
      String.replace(File.read!(facade), "LynxIoFixture", "LynxPositionalFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Positional"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      cargo: [features: ["positional-file"]],
      only: [open_slots: 0, patch_at: 3, observe_at: 2],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      proof_roots: ["io_protocol::write_then_sync"],
      module_prefix: "Positional.Extraction",
      lean_project: project,
      build_dir: Path.join(tmp, "build")
    ]
  end

  defp write_proofs!(project, bindings, sources) do
    for {source, module} <- sources do
      content =
        File.read!(Path.join(@fixture, source))
        |> String.replace("Disk", "Positional")
        |> String.replace(
          "open Aeneas Aeneas.Std Lynx io_protocol",
          "open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol"
        )
        |> String.replace("io_protocol.io_core.", "io_native.io_core.")
        |> String.replace("io_protocol.positional.", "io_native.io_protocol.positional.")
        |> String.replace("__OPEN__", bindings["open_slots"]["lean_name"])
        |> String.replace("__PATCH__", bindings["patch_at"]["lean_name"])
        |> String.replace("__OBSERVE__", bindings["observe_at"]["lean_name"])

      File.write!(Path.join(project, "Positional/#{module}.lean"), content)
    end
  end

  defp load_and_calibrate(prepared, tmp) do
    library = Path.join(tmp, "positional-native")
    File.cp!(prepared.library, library <> ".so")
    source = Path.join(tmp, "native.ex")

    stubs =
      for {name, arity, _flags} <- prepared.bindings.exports do
        "def #{name}(#{Enum.join(List.duplicate("_", arity), ", ")}), do: :erlang.nif_error(:not_loaded)"
      end

    File.write!(source, """
    defmodule LynxPositionalFixture.Native do
      @compile :debug_info
      @on_load :load
      def load, do: :erlang.load_nif(~c"#{library}", 0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    on_exit(fn ->
      :code.delete(LynxPositionalFixture.Native)
      :code.purge(LynxPositionalFixture.Native)
    end)

    assert {:ok, [LynxPositionalFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(source, tmp, LynxPositionalFixture.Native)

    script = Path.join(tmp, "calibrate.exs")

    File.write!(script, """
    alias LynxPositionalFixture.Native
    true = try do
      Native.open_slots()
      false
    catch
      :error, :open_failed -> true
    end
    File.write!("slots", <<1, 2>>)
    file = Native.open_slots()
    reader = Native.open_slots()
    false = file == reader
    true = Native.patch_at(file, 4, 9)
    9 = Native.observe_at(reader, 4)
    nil = Native.observe_at(file, 5)
    1 = Native.observe_at(file, 0)
    true = try do
      Native.patch_at(file, -1, 9)
      false
    catch
      :error, :badarg -> true
    end
    <<1, 2, 0, 0, 9>> = File.read!("slots")

    File.write!("slots", <<1, 2>>)
    peer = Task.async(fn -> Native.patch_at(reader, 0, 7) end)
    true = Native.patch_at(file, 0, 9)
    true = Task.await(peer)
    observed = Native.observe_at(file, 0)
    true = observed in [7, 9]
    <<^observed, 2>> = File.read!("slots")
    """)

    {output, status} =
      System.cmd("elixir", ["--erl", "+S 2:2", "-r", source, script],
        cd: tmp,
        stderr_to_stdout: true
      )

    assert status == 0, output
  end
end
