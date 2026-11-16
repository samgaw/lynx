defmodule Lynx.Rustler.CapturedFramesTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RUNTIME_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RUNTIME_DIR for captured parser composition")

  @tag :tmp_dir
  test "composes an original parser certificate with captured callers and guard cleanup", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = project(tmp, "standalone")

    for {source, target} <- [
          {"FrameRuntimeProperties.lean", "Properties.lean"},
          {"CheckedFrameProperties.lean", "CheckedProperties.lean"},
          {"CapturedFrameProperties.lean", "CapturedProperties.lean"}
        ] do
      File.cp!(Path.join(@fixture, source), Path.join(project, "FrameRuntime/" <> target))
    end

    rust = [
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      roots: ["atomic_analysis::guard_frame"],
      lean_project: project,
      module_prefix: "FrameRuntime.Extraction",
      build_dir: Path.join(tmp, "rust-build"),
      proof_modules: [
        "FrameRuntime.Properties",
        "FrameRuntime.CheckedProperties",
        "FrameRuntime.CapturedProperties"
      ],
      required_properties:
        ~w(FrameRuntime.Properties.no_panic FrameRuntime.Properties.split_panic FrameRuntime.Properties.consumes_exact FrameRuntime.CheckedProperties.checked_contract FrameRuntime.CheckedProperties.checked_consumes_exact FrameRuntime.CapturedProperties.guard_contract FrameRuntime.CapturedProperties.guard_consumes_exact FrameRuntime.CapturedProperties.guard_heap),
      nonpanicking: [{"atomic_core::frames::take_frame", "FrameRuntime.Properties.no_panic"}]
    ]

    result = Lynx.Rust.verify!(workspace, "atomic-analysis", rust)
    assert [%{status: :ok}] = result.reports
    assert length(result.extraction.captured_unwind) == 3

    protected =
      for {id, f} <- result.extraction.implementations,
          f["rust_name"] in [
            "atomic_core::frames::take_frame",
            "atomic_core::frames::split_buffer"
          ],
          do: id

    assert length(protected) == 2
    refute Enum.any?(result.extraction.captured_unwind, &(&1.function_id in protected))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "atomic-analysis", rust).reports

    export = Path.join(tmp, "rust.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, rust[:proof_modules])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    check_export(project, export)

    assert_raise CompileError, ~r/captured unwind requires/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", Keyword.delete(rust, :nonpanicking))
    end

    analysis = Path.join(workspace, "analysis/src/lib.rs")
    original = File.read!(analysis)

    File.write!(
      analysis,
      original <>
        """

        pub fn direct_split(input: &mut Vec<u8>, position: usize) -> Vec<u8> {
            atomic_core::frames::split_buffer(input, position)
        }
        """
    )

    assert_raise CompileError, ~r/actual nonpanicking or captured first-party callees/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "atomic-analysis",
        Keyword.update!(rust, :roots, &(&1 ++ ["atomic_analysis::direct_split"]))
      )
    end

    File.write!(analysis, original)

    File.write!(Path.join(project, "FrameRuntime/FalseCertificate.lean"), """
    module
    public import FrameRuntime.Extraction.Funs
    public section
    open Aeneas Aeneas.Std Lynx atomic_analysis
    namespace FrameRuntime.FalseCertificate
    theorem claim (accepted : Bool) :
      (∃ result, atomic_core.accept_frame accepted = NativeM.ok result) ∨
        atomic_core.accept_frame accepted = Lynx.Result.error .exhausted := by
      cases accepted <;> simp [atomic_core.accept_frame, NativeM.massert, NativeM.fail, NativeM.ok, NativeM.lift]
    end FrameRuntime.FalseCertificate
    """)

    false_certificate =
      rust
      |> Keyword.put(
        :proof_modules,
        ["FrameRuntime.Properties", "FrameRuntime.FalseCertificate"]
      )
      |> Keyword.put(:required_properties, ["FrameRuntime.Properties.no_panic"])
      |> Keyword.update!(
        :nonpanicking,
        &(&1 ++ [{"atomic_core::accept_frame", "FrameRuntime.FalseCertificate.claim"}])
      )

    failed_claim =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "atomic-analysis", false_certificate)
      end

    assert failed_claim.message =~ "FalseCertificate"
    assert failed_claim.message =~ "unsolved goals"

    project = project(tmp, "nif")
    File.mkdir_p!(Path.join(project, "CapturedFrames"))

    parser =
      File.read!(Path.join(@fixture, "FrameRuntimeProperties.lean"))
      |> String.replace("FrameRuntime", "CapturedFrames")
      |> String.replace(
        "open Aeneas Aeneas.Std atomic_analysis",
        "open Aeneas Aeneas.Std atomic_nif"
      )

    properties =
      File.read!(Path.join(@fixture, "CheckedFrameProperties.lean"))
      |> String.replace("FrameRuntime", "CapturedFrames")
      |> String.replace(
        "open Aeneas Aeneas.Std Lynx atomic_analysis",
        "open Aeneas Aeneas.Std Lynx atomic_nif atomic_nif.atomic_analysis"
      )

    File.write!(Path.join(project, "CapturedFrames/Properties.lean"), parser)
    File.write!(Path.join(project, "CapturedFrames/CheckedProperties.lean"), properties)
    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxAtomicFixture", "LynxCapturedFrameFixture")
    )

    options = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["captured-frames"]],
      root_attribute: "lynx::captured_frames",
      only: [captured_frame: 2],
      lean_project: project,
      module_prefix: "CapturedFrames.Extraction",
      build_dir: Path.join(tmp, "nif-build"),
      proof_modules: ["CapturedFrames.Properties", "CapturedFrames.CheckedProperties"],
      required_properties:
        ~w(CapturedFrames.Properties.no_panic CapturedFrames.Properties.split_panic CapturedFrames.Properties.consumes_exact CapturedFrames.CheckedProperties.checked_contract CapturedFrames.CheckedProperties.checked_consumes_exact),
      nonpanicking: [{"atomic_core::frames::take_frame", "CapturedFrames.Properties.no_panic"}]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert [%{"name" => "captured_frame", "arity" => 2, "flags" => 1, "captured_unwind" => true}] =
             prepared.bindings.bindings

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    stub =
      File.read!(Path.join(workspace, "elixir/native.ex"))
      |> String.replace("LynxAtomicFixture", "LynxCapturedFrameFixture")
      |> String.replace(
        "\nend\n",
        "\n  def captured_frame(_, _), do: :erlang.nif_error(:not_loaded)\nend\n"
      )

    Code.compile_string(stub, Path.join(workspace, "elixir/native.ex"))
    [{module, beam}] = Code.compile_file(Path.join(workspace, "elixir/captured_frame_laws.ex"))

    for law <- ~w(complete incomplete wrong_version empty rejected badarg)a,
        do: assert(apply(module, law, []))

    laws = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 16384, maxHeartbeats: 12_000_000]
    ]

    export = Path.join(tmp, "laws.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(laws, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 6
    check_export(project, export)
    assert Enum.all?(Lynx.Laws.verify([beam], laws), &(&1.status == :ok and &1.cached))

    proof = Path.join(project, "CapturedFrames/CheckedProperties.lean")

    for invalid <- [
          properties <> "\nprivate axiom unchecked_frame : False\n",
          properties <> "\nprivate theorem unfinished_frame : True := by sorry\n"
        ] do
      File.write!(proof, invalid)
      assert_raise RuntimeError, ~r/audit failed/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(proof, properties)
    core = Path.join(workspace, "core/src/frames.rs")
    original = File.read!(core)

    File.write!(
      core,
      String.replace(original, "if input.len() < 3 {", "if input.len() < 3 { panic!();")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(
      core,
      String.replace(
        original,
        "std::mem::replace(input, suffix)",
        "std::mem::replace(input, Vec::new())"
      )
    )

    lost_tail =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert lost_tail.message =~ "CapturedFrames/Properties.lean"
    assert lost_tail.message =~ "⊢ tail = []"
    File.write!(core, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end

  defp project(tmp, name) do
    project = Path.join(tmp, name)
    File.mkdir_p!(Path.join(project, "FrameRuntime"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    project
  end

  defp check_export(project, export) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
