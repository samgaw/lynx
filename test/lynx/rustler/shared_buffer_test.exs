defmodule Lynx.Rustler.SharedBufferTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_BUFFER_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_NATIVE_BUFFER_DIR for persistent buffer resource proofs")

  @tag :tmp_dir
  test "verifies shared vector state, concurrent callers and linked nested cleanup", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxAtomicFixture", "LynxSharedBufferFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "SharedBytes"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    base = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      branching: :duplicate,
      root_attribute: "lynx::shared_buffer",
      lean_project: project,
      module_prefix: "SharedBytes.Extraction",
      build_dir: Path.join(tmp, "build"),
      only: [shared_new: 0, shared_append: 2, shared_read: 1]
    ]

    prepared = Lynx.Rustler.prepare!(base)

    File.cp!(
      Path.join(@fixture, "SharedBytesProperties.lean"),
      Path.join(project, "SharedBytes/Properties.lean")
    )

    nif =
      Enum.reduce(
        [{"NEW", "shared_new"}, {"APPEND", "shared_append"}, {"READ", "shared_read"}],
        File.read!(Path.join(@fixture, "SharedBytesNifProperties.lean")),
        fn {key, name}, text ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(text, "__#{key}__", binding["lean_name"])
        end
      )

    File.write!(Path.join(project, "SharedBytes/NifProperties.lean"), nif)

    options =
      base ++
        [
          proof_modules: ["SharedBytes.Properties", "SharedBytes.NifProperties"],
          required_properties:
            Enum.map(
              ~w(append_eq payload_cleanup cleanup_contract cleanup_run append_contract append_run head_eq read_contract read_run final_release),
              &("SharedBytes.Properties." <> &1)
            ) ++
              Enum.map(
                ~w(create_contract append_contract read_contract),
                &("SharedBytes.NifProperties." <> &1)
              )
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    assert Enum.any?(
             checked.verification.resource_cleanup,
             &(&1.lean_name == "atomic_nif.SharedBuffer.drop_owned")
           )

    file = Lynx.Rust.Proofs.file!(checked.extraction, options[:proof_modules])
    export = Path.join(tmp, "native.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    check_export(project, export)

    # Removing the concrete payload dictionary must not select a no-drop fallback.
    funs = Path.join(project, "SharedBytes/Extraction/Funs.lean")
    original = File.read!(funs)

    missing =
      Regex.replace(
        ~r/instance : Lynx.NativeMutexDrop atomic_nif\.atomic_analysis\.ReceiveState where\n  drop :=[^\n]+\n/,
        original,
        ""
      )

    refute missing == original
    File.write!(funs, missing)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["SharedBytes.Extraction.Funs"])
    end

    File.write!(funs, original)
    Lynx.Rust.Project.build!(project, ["SharedBytes.Extraction.Funs"])

    core = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(core)

    wrong =
      String.replace(
        rust,
        "output.extend_from_slice(input);",
        "output.extend_from_slice(input); output.extend_from_slice(input);"
      )

    refute wrong == rust
    File.write!(core, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, rust)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

    File.write!(
      core,
      rust <> "\nimpl Drop for BufferState { fn drop(&mut self) { self.bytes.push(1); } }\n"
    )

    assert_raise CompileError, ~r/resource call requires|native destruction/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, rust)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxSharedBufferFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    [{module, beam}] = Code.compile_file(Path.join(workspace, "elixir/shared_buffer_laws.ex"))

    for law <-
          ~w(empty appends alias_observes rejected_input_preserves invalid_handle concurrent_appends)a,
        do: assert(apply(module, law, []))

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 8192, maxHeartbeats: 24_000_000]
    ]

    law_export = Path.join(tmp, "laws.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, law_export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 6
    check_export(project, law_export)
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
  end

  @tag :tmp_dir
  test "links owning payload destruction across crates without Rustler", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "OwnedBuffer"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    File.write!(Path.join(project, "OwnedBuffer/Properties.lean"), """
    module
    public import OwnedBuffer.Extraction.Funs
    public section
    open Aeneas Aeneas.Std Lynx atomic_analysis
    namespace OwnedBuffer.Properties
    theorem disposed (mutex : NativeMutex ReceiveState)
        (value : ReceiveState) (poisoned : Bool) (env : Environment)
        (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
          [(mutex.id, NativeMutex.typeName ReceiveState, .tuple #[.atom "unlocked",
            .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
        (schedule : List ScheduleChoice) :
        (atomic_analysis.dispose_receive_state mutex).run env schedule =
          (.ok (), {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != mutex.id)}) := by
      cases poisoned <;>
        simp [atomic_analysis.dispose_receive_state, NativeOwnedDrop.drop, NativeMutexDrop.drop,
          NativeMutex.disposeWith, ReceiveState.drop_owned,
          NativeMutex.into_inner, NativeMutex.intoInnerStep, stored, NativeCodec.roundtrip,
          NativeM.ok, Result.wait_run, Result.wait_bind]
    end OwnedBuffer.Properties
    """)

    options = [
      roots: ["atomic_analysis::dispose_receive_state"],
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      lean_project: project,
      module_prefix: "OwnedBuffer.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["OwnedBuffer.Properties"],
      required_properties: ["OwnedBuffer.Properties.disposed"]
    ]

    result = Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    export = Path.join(tmp, "native.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    check_export(project, export)
    source = Path.join(workspace, "analysis/src/lib.rs")
    rust = File.read!(source)

    wrong =
      String.replace(rust, "    drop(state);", "    drop(state);\n    panic!(\"after cleanup\");")

    refute wrong == rust
    File.write!(source, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports
  end

  defp check_export(project, file) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", file] ++ sandbox)
    assert status == 0, output
  end
end
