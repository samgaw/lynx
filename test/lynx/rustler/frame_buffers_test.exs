defmodule Lynx.Rustler.FrameBuffersTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_BUFFER_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_NATIVE_BUFFER_DIR for compiled frame NIF proofs")

  @tag :tmp_dir
  test "proves frame boundaries, byte retention, decoder failures and panics through Rustler", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxAtomicFixture", "LynxFrameFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Frames"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    base = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      mir: :optimized,
      branching: :duplicate,
      root_attribute: "lynx::frames",
      only: [frame_summary: 1, frame_split: 2],
      lean_project: project,
      module_prefix: "Frames.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert [
             %{
               "name" => "frame_summary",
               "arity" => 1,
               "flags" => 1,
               "arguments" => ["binary"],
               "result" => %{"tuple" => ["u8", "u64", "u64"]}
             },
             %{
               "name" => "frame_split",
               "arity" => 2,
               "flags" => 0,
               "arguments" => ["binary", "u16"],
               "result" => %{"tuple" => ["u64", "u64"]}
             }
           ] = prepared.bindings.bindings

    File.read!(Path.join(@fixture, "FrameProperties.lean"))
    |> String.replace("SplitBuffer.", "Frames.")
    |> String.replace(
      "open Aeneas Aeneas.Std atomic_analysis",
      "open Aeneas Aeneas.Std atomic_nif atomic_nif.atomic_analysis"
    )
    |> then(&File.write!(Path.join(project, "Frames/Properties.lean"), &1))

    proof =
      Enum.reduce(
        [{"SUMMARY", "frame_summary"}, {"SPLIT", "frame_split"}],
        File.read!(Path.join(@fixture, "FrameNifProperties.lean")),
        fn {key, name}, text ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(text, "__#{key}__", binding["lean_name"])
        end
      )

    File.write!(Path.join(project, "Frames/NifProperties.lean"), proof)

    options =
      base ++
        [
          proof_modules: ["Frames.Properties", "Frames.NifProperties"],
          required_properties:
            Enum.map(
              ~w(split_exact split_panic split_cutoff split_preserves_bytes short wrong_version truncated consumes_exact),
              &("Frames.Properties." <> &1)
            ) ++
              Enum.map(
                ~w(summary_contract summary_empty summary_frame summary_truncated summary_bad_version summary_zero summary_network split_middle split_empty split_zero split_panic),
                &("Frames.NifProperties." <> &1)
              )
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    export = Path.join(tmp, "native.export")
    file = Lynx.Rust.Proofs.file!(checked.extraction, options[:proof_modules])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    check_export(project, export)

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(checked.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxFrameFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    [{module, beam}] = Code.compile_file(Path.join(workspace, "elixir/frame_laws.ex"))

    for law <-
          ~w(empty one_frame truncated wrong_version empty_payload network_order split_middle split_empty decoder_narrows split_panics decoder_rejects rejects_nonbinary)a,
        do: assert(apply(module, law, []))

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        options: [maxRecDepth: 8192],
        export: Path.join(tmp, "laws.export")
      )

    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 12
    check_export(project, Path.join(tmp, "laws.export"))

    assert Enum.all?(
             Lynx.Laws.verify([beam],
               native: {Lynx.Rustler, options},
               options: [maxRecDepth: 8192]
             ),
             &(&1.status == :ok and &1.cached)
           )

    # The full module remains audited, including unused private declarations.
    original = File.read!(Path.join(project, "Frames/NifProperties.lean"))

    for unfinished <- [
          "private axiom unapproved : False",
          "private theorem unfinished : False := by sorry"
        ] do
      File.write!(
        Path.join(project, "Frames/NifProperties.lean"),
        original <> "\n" <> unfinished <> "\n"
      )

      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(Path.join(project, "Frames/NifProperties.lean"), original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end

  defp check_export(project, file) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", file] ++ sandbox)
    assert status == 0, output
  end
end
