defmodule Lynx.Rustler.CapturedSharedFramesTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_OWNED_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_OWNED_DIR for persistent captured frame proofs")

  @tag :tmp_dir
  test "preserves persistent buffer state and resource owners across captured parser panics", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxAtomicFixture", "LynxCapturedSharedFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "CapturedShared"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    for {source, target} <- [
          {"FrameRuntimeProperties.lean", "Properties.lean"},
          {"CheckedFrameProperties.lean", "CheckedProperties.lean"},
          {"CapturedFrameProperties.lean", "CapturedProperties.lean"}
        ] do
      proof =
        File.read!(Path.join(@fixture, source))
        |> String.replace("FrameRuntime", "CapturedShared")
        |> String.replace(
          "open Aeneas Aeneas.Std atomic_analysis",
          "open Aeneas Aeneas.Std atomic_nif"
        )
        |> String.replace(
          "open Aeneas Aeneas.Std Lynx atomic_analysis",
          "open Aeneas Aeneas.Std Lynx atomic_nif atomic_nif.atomic_analysis"
        )
        |> String.replace("NativeDrop.drop", "NativeOwnedDrop.drop")
        |> String.replace(
          "NativeUnwindDrop.drop",
          "NativeResourceUnwindDrop.drop, NativeUnwindDrop.drop"
        )

      File.write!(Path.join(project, "CapturedShared/" <> target), proof)
    end

    options = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      owned_drops: true,
      branching: :duplicate,
      cargo: [features: ["captured-resources"]],
      root_attribute: "lynx::captured_shared",
      only: [shared_new: 0, shared_append: 2, shared_read: 1, shared_checked_frame: 2],
      lean_project: project,
      module_prefix: "CapturedShared.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: [
        "CapturedShared.Properties",
        "CapturedShared.CheckedProperties",
        "CapturedShared.CapturedProperties"
      ],
      required_properties:
        ~w(CapturedShared.Properties.no_panic CapturedShared.Properties.consumes_exact CapturedShared.CapturedProperties.guard_heap CapturedShared.CapturedProperties.guard_consumes_exact),
      nonpanicking: [{"atomic_core::frames::take_frame", "CapturedShared.Properties.no_panic"}]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))
    binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == "shared_checked_frame"))

    assert %{
             "arity" => 2,
             "flags" => 1,
             "captured_unwind" => true,
             "rust_name" => "checked_shared_frame_request"
           } = binding

    assert Enum.any?(prepared.extraction.native_drops, & &1.unwind)

    proof =
      File.read!(Path.join(@fixture, "CapturedSharedNifProperties.lean"))
      |> String.replace("__FRAME__", binding["lean_name"])
      |> String.replace(
        "__NEW__",
        Enum.find(prepared.bindings.bindings, &(&1["name"] == "shared_new"))["lean_name"]
      )

    property = Path.join(project, "CapturedShared/NifProperties.lean")
    File.write!(property, proof)
    options = Keyword.update!(options, :proof_modules, &(&1 ++ ["CapturedShared.NifProperties"]))

    options =
      Keyword.update!(
        options,
        :required_properties,
        &(&1 ++
            ~w(CapturedShared.NifProperties.frame_contract CapturedShared.NifProperties.payload_cleanup CapturedShared.NifProperties.new_unregistered))
      )

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(checked.library, Path.join(workspace, "priv/libatomic_nif.so"))

    stub =
      File.read!(Path.join(workspace, "elixir/native.ex"))
      |> String.replace("LynxAtomicFixture", "LynxCapturedSharedFixture")
      |> String.replace(
        "\nend\n",
        "\n  def shared_checked_frame(_, _), do: :erlang.nif_error(:not_loaded)\nend\n"
      )

    Code.compile_string(stub, Path.join(workspace, "elixir/native.ex"))
    [{module, beam}] = Code.compile_file(Path.join(workspace, "elixir/captured_shared_laws.ex"))

    for law <-
          ~w(successive_frames rejected_consumes incomplete_failure_retains decoder_failure_preserves malformed_preserves)a,
        do: assert(apply(module, law, []))

    laws = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 16384, maxHeartbeats: 24_000_000]
    ]

    export = Path.join(tmp, "laws.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(laws, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 5
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    assert Enum.all?(Lynx.Laws.verify([beam], laws), &(&1.status == :ok and &1.cached))

    raw = File.read!(checked.extraction.llbc) |> JSON.decode!()

    missing =
      update_in(raw, ["translated", "fun_decls"], fn functions ->
        Enum.map(functions, fn function ->
          if function &&
               List.last(function["item_meta"]["name"]) == %{"Ident" => ["drop_owned", 0]},
             do: Map.put(function, "body", "Opaque"),
             else: function
        end)
      end)

    assert_raise CompileError, ~r/unsupported resource destructor|unsupported native drop/, fn ->
      Lynx.Rust.NativeDropLowering.lower!(missing, checked.extraction.audit.first_party,
        unwind: :captured
      )
    end

    for extra <- [
          "private axiom hidden_native_escape : False",
          "private theorem unfinished_native : True := by sorry"
        ] do
      File.write!(property, proof <> "\n" <> extra)

      assert_raise RuntimeError, ~r/proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, proof)

    native = File.read!(source)

    File.write!(
      source,
      native <>
        "\nimpl Drop for SharedBuffer { fn drop(&mut self) { panic!(\"custom resource cleanup\"); } }\n"
    )

    assert_raise CompileError, ~r/unsupported resource destructor|unsupported native drop/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(source, native)

    core = Path.join(workspace, "core/src/frames.rs")
    original = File.read!(core)

    changed =
      String.replace(
        original,
        "std::mem::replace(input, suffix)",
        "std::mem::replace(input, Vec::new())"
      )

    refute changed == original
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
