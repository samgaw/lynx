defmodule Lynx.Rustler.LockedBufferCopyTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_BUFFER_DIR")
  @moduletag timeout: 1_800_000
  unless @tools, do: @moduletag(skip: "set LYNX_NATIVE_BUFFER_DIR for owned mutex buffer proofs")
  @properties ~w(append_eq take_run locked_contract locked_run copy_run)

  @tag :tmp_dir
  test "proves mutex byte handoff independently of Rustler and rejects changed implementations",
       %{tmp_dir: tmp} do
    workspace = workspace(tmp)
    project = project(tmp)
    property = Path.join(project, "LockedBytes/Properties.lean")

    original =
      File.read!(Path.join(@fixture, "LockedBytesProperties.lean"))
      |> String.replace("Lynx atomic_nif", "Lynx atomic_analysis")

    File.write!(property, original)

    options = [
      roots: ["atomic_analysis::copy_locked"],
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      branching: :duplicate,
      lean_project: project,
      module_prefix: "LockedBytes.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["LockedBytes.Properties"],
      required_properties: properties()
    ]

    result = Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "Consuming Mutex::into_inner")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports

    independent!(project, result.extraction, options[:proof_modules], tmp)

    core = Path.join(workspace, "core/src/lib.rs")
    source = File.read!(core)

    wrong =
      String.replace(source, "Ok(value) => value,", "Ok(mut value) => { value.push(0); value },")

    refute wrong == source
    File.write!(core, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    end

    File.write!(core, source)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports

    audit = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])

    for extra <- [
          "private axiom unprovedHandoff : False",
          "private theorem unfinishedHandoff : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [audit])
    end

    File.write!(property, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports
  end

  @tag :tmp_dir
  test "verifies the locked Rust copy through compiled Rustler adapters and ordinary laws", %{
    tmp_dir: tmp
  } do
    workspace = workspace(tmp)
    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxAtomicFixture", "LynxLockedBufferFixture")
    )

    project = project(tmp)

    base = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      branching: :duplicate,
      root_attribute: "lynx::locked_copy",
      lean_project: project,
      module_prefix: "LockedBytes.Extraction",
      build_dir: Path.join(tmp, "build"),
      only: [buffer_copy_locked: 1, buffer_length: 1, buffer_head: 1]
    ]

    prepared = Lynx.Rustler.prepare!(base)
    copy = Enum.find(prepared.bindings.bindings, &(&1["name"] == "buffer_copy_locked"))
    assert %{"name" => "buffer_copy_locked", "flags" => 1} = copy

    File.cp!(
      Path.join(@fixture, "LockedBytesProperties.lean"),
      Path.join(project, "LockedBytes/Properties.lean")
    )

    File.write!(
      Path.join(project, "LockedBytes/NifProperties.lean"),
      File.read!(Path.join(@fixture, "LockedBytesNifProperties.lean"))
      |> String.replace("__COPY__", copy["lean_name"])
    )

    options =
      base ++
        [
          proof_modules: ["LockedBytes.Properties", "LockedBytes.NifProperties"],
          required_properties: properties() ++ ["LockedBytes.NifProperties.facade_view"]
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))

    assert [%{lean_name: "atomic_nif.ByteBuffer.drop_owned"}] =
             checked.verification.resource_cleanup

    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    independent!(project, checked.extraction, options[:proof_modules], tmp)
    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxLockedBufferFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    native = LynxLockedBufferFixture.Native

    for bytes <- [<<>>, <<1, 2, 3>>, <<255, 128, 0>>] do
      resource = apply(native, :buffer_copy_locked, [bytes])
      assert apply(native, :buffer_length, [resource]) == byte_size(bytes)

      assert apply(native, :buffer_head, [resource]) ==
               if(bytes == <<>>, do: 0, else: :binary.first(bytes))
    end

    [{module, beam}] = Code.compile_file(Path.join(workspace, "elixir/locked_buffer_laws.ex"))

    for law <- ~w(copies empty raw_bytes independent_buffers rejects_list rejects_bits)a,
        do: assert(apply(module, law, []))

    export = Path.join(tmp, "laws.export")

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 8192, maxHeartbeats: 16_000_000]
    ]

    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 6
    check_export!(project, export)
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

    # Payload transfer must not silently admit unlinked nested destruction.
    original = File.read!(source)

    File.write!(
      source,
      original <>
        """

        pub struct MissingCleanup { pub bytes: std::sync::Mutex<Vec<u8>> }
        #[rustler::resource_impl]
        impl rustler::Resource for MissingCleanup {}
        #[rustler::nif(name = "missing_cleanup")]
        #[lynx::unlinked_cleanup]
        fn missing_cleanup() -> rustler::ResourceArc<MissingCleanup> {
            rustler::ResourceArc::new(MissingCleanup {
                bytes: std::sync::Mutex::new(Vec::new()),
            })
        }
        """
    )

    rejected =
      base
      |> Keyword.put(:only, missing_cleanup: 0)
      |> Keyword.put(:root_attribute, "lynx::unlinked_cleanup")

    assert_raise CompileError, ~r/resource call requires.*owning destructor/, fn ->
      Lynx.Rustler.prepare!(rejected)
    end

    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end

  defp properties, do: Enum.map(@properties, &("LockedBytes.Properties." <> &1))

  defp workspace(tmp) do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    workspace
  end

  defp project(tmp) do
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "LockedBytes"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.cp!(
      Path.join(@fixture, "LockedBytesModelTests.lean"),
      Path.join(project, "LockedBytes/ModelTests.lean")
    )

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    project
  end

  defp independent!(project, extraction, modules, tmp) do
    file = Lynx.Rust.Proofs.file!(extraction, modules)
    export = Path.join(tmp, "native.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    check_export!(project, export)
  end

  defp check_export!(project, export) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
