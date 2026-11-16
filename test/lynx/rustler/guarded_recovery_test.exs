defmodule Lynx.Rustler.GuardedRecoveryTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_FILE_AWAIT_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_FILE_AWAIT_DIR for compiled NIF crash recovery proofs")

  @tag :tmp_dir
  test "composes compiled synchronization and fresh recovery adapters through modelled restart",
       %{
         tmp_dir: tmp
       } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    native = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      native,
      String.replace(File.read!(native), "LynxIoFixture", "LynxGuardedRecoveryFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "GuardedRecovery"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    for {source, target} <- [
          {"GuardedRecoveryProperties.lean", "Properties.lean"},
          {"GuardedRecoveryWriterProperties.lean", "Writer.lean"},
          {"GuardedSyncProperties.lean", "Sync.lean"}
        ] do
      contents =
        File.read!(Path.join(@fixture, source))
        |> String.replace("GuardedSync.Extraction", "GuardedRecovery.Extraction")
        |> String.replace("GuardedSync.Properties", "GuardedRecovery.SyncProperties")
        |> String.replace(
          "open Aeneas Aeneas.Std Lynx io_protocol",
          "open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol"
        )

      File.write!(Path.join(project, "GuardedRecovery/" <> target), contents)
    end

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      cargo: [features: ["async-recovery"]],
      only: [async_log_open: 0, async_log_sync: 4, async_log_recover: 0],
      execution: :runtime,
      files: :regular,
      futures: :cancelling,
      owned_drops: true,
      branching: :duplicate,
      lean_project: project,
      module_prefix: "GuardedRecovery.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: [
        "GuardedRecovery.Properties",
        "GuardedRecovery.Writer",
        "GuardedRecovery.Sync"
      ],
      required_properties: ~w(GuardedRecovery.Properties.recovery_after_restart
        GuardedRecovery.Writer.every_acknowledged_recovery),
      nonpanicking: [{"io_protocol::poll_locked_sync", "GuardedRecovery.SyncProperties.no_panic"}]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == "async_log_recover"))
    assert %{"rust_name" => "recover_request", "arity" => 0, "flags" => 2} = binding
    property = Path.join(project, "GuardedRecovery/NifProperties.lean")

    File.write!(
      property,
      File.read!(Path.join(@fixture, "GuardedRecoveryNifProperties.lean"))
      |> String.replace("__RECOVER__", binding["lean_name"])
    )

    options =
      options
      |> Keyword.update!(:proof_modules, &(&1 ++ ["GuardedRecovery.NifProperties"]))
      |> Keyword.update!(
        :required_properties,
        &(&1 ++ ~w(GuardedRecovery.NifProperties.recover_contract
        GuardedRecovery.NifProperties.recover_facade_at_restart))
      )

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    adapter = adapter_proof(checked)
    file = prefix_proof(adapter)
    export = Path.join(tmp, "composition.export")

    reports =
      Lynx.Commands.verify!(project, verification_files(checked, [adapter, file]), export: export)

    assert_ok(reports)
    check_export(project, export)

    assert Enum.all?(
             Lynx.Commands.verify!(project, verification_files(checked, [adapter, file])),
             &(&1.status == :ok and &1.cached)
           )

    for extra <- [
          "private axiom assumed_restart : False",
          "private theorem unfinished_recovery : True := by sorry"
        ] do
      injected = update_in(file, ["preludes", Access.at(0), "source"], &(&1 <> "\n" <> extra))
      reports = Lynx.Commands.verify!(project, verification_files(checked, [adapter, injected]))
      assert Enum.any?(reports, &(&1.status == :error))

      assert Enum.any?(
               Enum.flat_map(reports, & &1.diagnostics),
               &(String.contains?(&1.message, "axiom") or String.contains?(&1.message, "sorry"))
             )
    end

    wrong_bound =
      update_in(file, ["preludes", Access.at(0), "source"], fn source ->
        String.replace(source, "highWater + 4 &&", "highWater + 3 &&", global: false)
      end)

    refute wrong_bound == file
    rejected = Lynx.Commands.verify!(project, verification_files(checked, [adapter, wrong_bound]))
    assert Enum.any?(rejected, &(&1.status == :error))

    assert Enum.any?(
             Enum.flat_map(rejected, & &1.diagnostics),
             &String.contains?(&1.message, "unsolved goals")
           )

    library = Path.join(tmp, "librecovery")
    File.cp!(checked.library, library <> ".so")
    [{module, exports}] = Map.to_list(checked.external.native_exports)
    assert module == LynxGuardedRecoveryFixture.Native

    functions =
      Enum.map_join(exports, "\n", fn {name, arity} ->
        "def #{name}(#{Enum.join(List.duplicate("_", arity), ", ")}), do: :erlang.nif_error(:not_loaded)"
      end)

    Code.compile_string("""
    defmodule #{inspect(module)} do
      @compile :debug_info
      @on_load :load
      def load, do: :erlang.load_nif(to_charlist(#{JSON.encode!(library)}), 0)
      #{functions}
    end
    """)

    beams = Code.compile_file(Path.join(@fixture, "GuardedRecoveryLaws.exs"))
    runtime = Path.join(tmp, "runtime")
    File.mkdir_p!(runtime)

    File.cd!(runtime, fn ->
      File.write!("journal", <<1>>)
      assert apply(LynxGuardedRecoveryFixture.WriterLaws, :acknowledged_prefix, [])
      assert apply(LynxGuardedRecoveryFixture.CompleteLaws, :recover_acknowledged_words, [])
      File.write!("journal", <<1>>)
      assert apply(LynxGuardedRecoveryFixture.TruncatedLaws, :reject_truncated_words, [])
      File.rm!("journal")
      assert apply(LynxGuardedRecoveryFixture.DeniedLaws, :report_open_failure, [])
    end)

    for {module, beam} <- beams do
      initial =
        case module do
          LynxGuardedRecoveryFixture.WriterLaws ->
            "GuardedRecovery.NifProperties.writerInitial"

          LynxGuardedRecoveryFixture.CompleteLaws ->
            "GuardedRecovery.NifProperties.completeBoot"

          LynxGuardedRecoveryFixture.TruncatedLaws ->
            "GuardedRecovery.NifProperties.truncatedBoot"

          LynxGuardedRecoveryFixture.DeniedLaws ->
            "GuardedRecovery.NifProperties.denied"
        end

      laws = [
        native: {Lynx.Rustler, options},
        initial_environment: initial,
        options: [maxRecDepth: 16384, maxHeartbeats: 16_000_000]
      ]

      export = Path.join(tmp, Atom.to_string(module) <> ".export")
      reports = Lynx.Laws.verify([beam], Keyword.put(laws, :export, export))
      assert_ok(reports)
      assert length(Enum.flat_map(reports, & &1.theorems)) == 1
      check_export(project, export)
      assert Enum.all?(Lynx.Laws.verify([beam], laws), &(&1.status == :ok and &1.cached))
    end

    {_, denied} = Enum.find(beams, &(elem(&1, 0) == LynxGuardedRecoveryFixture.DeniedLaws))

    rejected =
      Lynx.Laws.verify([denied],
        native: {Lynx.Rustler, options},
        initial_environment: "GuardedRecovery.NifProperties.unadmitted",
        options: [maxRecDepth: 16384, maxHeartbeats: 16_000_000]
      )

    assert Enum.any?(rejected, &(&1.status == :error))

    source = Path.join(workspace, "protocol/src/lib.rs")
    valid = File.read!(source)
    [prefix, recovery] = String.split(valid, "pub fn reopen_words(", parts: 2)

    wrong =
      String.replace(recovery, "locked_word(&mutex, 2)", "locked_word(&mutex, 0)", global: false)

    refute recovery == wrong
    File.write!(source, prefix <> "pub fn reopen_words(" <> wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(source, valid)
    restored = Lynx.Rustler.prepare!(options)
    assert Enum.all?(restored.reports, &(&1.status == :ok))

    assert_ok(
      Lynx.Commands.verify!(
        project,
        verification_files(restored, [
          adapter_proof(restored),
          prefix_proof(adapter_proof(restored))
        ])
      )
    )
  end

  defp adapter_proof(checked) do
    adapter =
      Enum.find(checked.external.files, &String.ends_with?(&1["module"], "RustlerAdapter"))

    [_, namespace] = Regex.run(~r/^namespace (.+)$/m, hd(adapter["preludes"])["source"])
    modules = Enum.map(checked.external.files, & &1["module"])

    source =
      File.read!(Path.join(@fixture, "GuardedRecoveryAdapterProperties.lean"))
      |> String.replace(
        "__EXTERNAL_IMPORTS__",
        Enum.map_join(modules, "\n", &("public import " <> &1))
      )
      |> String.replace("__NAMESPACE__", namespace)

    name = "GuardedRecovery.AdapterProof"

    %{
      "module" => name,
      "file" => name <> ".lean",
      "imports" => modules,
      "contents" => [],
      "audit_modules" =>
        Enum.uniq([
          name | Enum.flat_map(checked.external.files, &Map.get(&1, "audit_modules", []))
        ]),
      "preludes" => [
        %{"source" => source, "file" => name <> ".lean", "span" => [1], "indentation" => 0}
      ]
    }
  end

  defp prefix_proof(adapter) do
    name = "GuardedRecovery.Interrupted"

    %{
      "module" => name,
      "file" => name <> ".lean",
      "imports" => [adapter["module"]],
      "contents" => [],
      "audit_modules" =>
        Enum.uniq([name, "Lynx.Term.NativeInvariant" | adapter["audit_modules"]]),
      "preludes" => [
        %{
          "source" => File.read!(Path.join(@fixture, "GuardedRecoveryPrefixProperties.lean")),
          "file" => name <> ".lean",
          "span" => [1],
          "indentation" => 0
        }
      ]
    }
  end

  defp verification_files(checked, proof) do
    Enum.map(checked.external.files ++ List.wrap(proof), fn file ->
      key = Lynx.Rust.Fingerprint.digest(JSON.encode!(file) <> checked.external.fingerprint)
      Map.put(file, "cache_key", key)
    end)
  end

  defp assert_ok(reports) do
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
  end

  defp check_export(project, export) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
