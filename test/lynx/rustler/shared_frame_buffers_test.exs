defmodule Lynx.Rustler.SharedFrameBuffersTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_BUFFER_DIR")
  @moduletag timeout: 1_800_000
  unless @tools, do: @moduletag(skip: "set LYNX_NATIVE_BUFFER_DIR for guarded parser proofs")

  @tag :tmp_dir
  test "composes checked parser bodies with persistent Rustler mutex state", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxAtomicFixture", "LynxSharedFrameFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "SharedFrames"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    proof = Path.join(project, "SharedFrames/ParserProperties.lean")

    parser =
      File.read!(Path.join(@fixture, "FrameRuntimeProperties.lean"))
      |> String.replace("FrameRuntime", "SharedFrames")
      |> String.replace(
        "namespace SharedFrames.Properties",
        "namespace SharedFrames.ParserProperties"
      )
      |> String.replace("end SharedFrames.Properties", "end SharedFrames.ParserProperties")
      |> String.replace(
        "open Aeneas Aeneas.Std atomic_analysis",
        "open Aeneas Aeneas.Std atomic_nif"
      )

    File.write!(proof, parser)

    options = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      branching: :duplicate,
      root_attribute: "lynx::shared_frames",
      only: [shared_new: 0, shared_append: 2, shared_read: 1, shared_frame: 1],
      lean_project: project,
      module_prefix: "SharedFrames.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["SharedFrames.ParserProperties"],
      nonpanicking: [
        {"atomic_core::frames::take_frame", "SharedFrames.ParserProperties.no_panic"}
      ]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert [
             %{
               rust: "atomic_core::frames::take_frame",
               theorem: "SharedFrames.ParserProperties.no_panic"
             }
           ] = prepared.verification.nonpanicking

    protected =
      for {id, implementation} <- prepared.extraction.implementations,
          implementation["rust_name"] in [
            "atomic_core::frames::take_frame",
            "atomic_core::frames::split_buffer"
          ],
          do: id

    assert length(protected) == 2
    refute Enum.any?(prepared.extraction.native_unwind, &(&1[:caller] in protected))
    assert Enum.any?(prepared.extraction.native_unwind, &(&1[:function] in protected))

    binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == "shared_frame"))

    nif =
      File.read!(Path.join(@fixture, "SharedFramesNifProperties.lean"))
      |> String.replace("__FRAME__", binding["lean_name"])

    File.write!(Path.join(project, "SharedFrames/NifProperties.lean"), nif)

    options =
      Keyword.merge(options,
        proof_modules: ["SharedFrames.ParserProperties", "SharedFrames.NifProperties"],
        required_properties:
          Enum.map(
            ~w(parse_contract frame_contract short_run wrong_version_run),
            &("SharedFrames.NifProperties." <> &1)
          )
      )

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxSharedFrameFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    [{module, beam}] = Code.compile_file(Path.join(workspace, "elixir/shared_frame_laws.ex"))

    for law <-
          ~w(successive_frames incomplete_then_complete malformed_preserves invalid_handle concurrent_frames)a,
        do: assert(apply(module, law, []))

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 8192, maxHeartbeats: 24_000_000]
    ]

    export = Path.join(tmp, "laws.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 5
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

    assert_raise CompileError, ~r/drop|borrowed native guard/, fn ->
      Lynx.Rustler.prepare!(Keyword.delete(options, :nonpanicking))
    end

    for certificate <- [
          "SharedFrames.ParserProperties.short",
          "SharedFrames.ParserProperties.missing"
        ] do
      assert_raise RuntimeError, ~r/audit failed/, fn ->
        Lynx.Rustler.prepare!(
          Keyword.put(options, :nonpanicking, [{"atomic_core::frames::take_frame", certificate}])
        )
      end
    end

    unfinished =
      Regex.replace(
        ~r/(theorem no_panic.*?:= by).*?end SharedFrames.ParserProperties/s,
        parser,
        fn _, statement -> statement <> "\n  sorry\nend SharedFrames.ParserProperties\n" end
      )

    refute unfinished == parser

    for invalid <- [
          unfinished,
          parser <> "\nprivate axiom unused_native_escape : False\n",
          String.replace(parser, "theorem no_panic", "def no_panic")
        ] do
      File.write!(proof, invalid)
      assert_raise RuntimeError, ~r/audit failed/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(proof, parser)

    core = Path.join(workspace, "core/src/frames.rs")
    rust = File.read!(core)

    changed =
      String.replace(
        rust,
        "if input.len() < 3 {",
        "if input.len() < 3 { let _ = split_buffer(input, 3);"
      )

    refute changed == rust
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, rust)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
