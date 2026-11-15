defmodule Lynx.Rustler.CapturedReplyTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RUNTIME_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RUNTIME_DIR for nested reply unwind proofs")

  @tag :tmp_dir
  test "preserves typed replies, mutations and guard cleanup across crates and Rustler", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock base app nif elixir),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = project(tmp, "standalone")
    properties = File.read!(Path.join(@fixture, "CapturedReplyProperties.lean"))
    File.mkdir_p!(Path.join(project, "CapturedReplies"))
    File.write!(Path.join(project, "CapturedReplies/Properties.lean"), properties)

    rust_options = [
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      roots: ["ownership_app::checked_reply", "ownership_app::guard_reply"],
      lean_project: project,
      module_prefix: "CapturedReplies.Extraction",
      build_dir: Path.join(tmp, "rust-build"),
      proof_modules: ["CapturedReplies.Properties"],
      required_properties:
        Enum.map(
          ~w(reply checked_reply guard_composes guard_heap),
          &("CapturedReplies.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "ownership-app", rust_options)
    assert [%{status: :ok}] = result.reports
    assert length(result.extraction.captured_unwind) == 3
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "ownership-app", rust_options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, rust_options[:proof_modules])
    export = Path.join(tmp, "rust.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    check_export(project, export)

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxCapturedReplyFixture")
    )

    project = project(tmp, "nif-proofs")
    File.mkdir_p!(Path.join(project, "ReplyNif"))

    nif_properties =
      properties
      |> String.replace("CapturedReplies", "ReplyNif")
      |> String.replace(
        "open Aeneas Aeneas.Std Lynx ownership_app",
        "open Aeneas Aeneas.Std Lynx ownership_nif ownership_nif.ownership_app"
      )

    File.write!(Path.join(project, "ReplyNif/Properties.lean"), nif_properties)

    options = [
      workspace: workspace,
      package: "ownership-nif",
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["captured-reply"]],
      root_attribute: "lynx::captured_reply",
      proof_roots: ["ownership_app::checked_reply"],
      only: [captured_reply: 4],
      lean_project: project,
      module_prefix: "ReplyNif.Extraction",
      build_dir: Path.join(tmp, "nif-build"),
      proof_modules: ["ReplyNif.Properties"],
      required_properties:
        Enum.map(
          ~w(reply checked_reply guard_composes guard_heap),
          &("ReplyNif.Properties." <> &1)
        )
    ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert [%{"name" => "captured_reply", "arity" => 4, "flags" => 1, "captured_unwind" => true}] =
             prepared.bindings.bindings

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))

    stub =
      File.read!(Path.join(workspace, "elixir/native.ex"))
      |> String.replace("LynxOwnershipFixture", "LynxCapturedReplyFixture")
      |> String.replace(
        "\nend\n",
        "\n  def captured_reply(_, _, _, _), do: :erlang.nif_error(:not_loaded)\nend\n"
      )

    Code.compile_string(stub, Path.join(workspace, "elixir/native.ex"))
    [{module, beam}] = Code.compile_file(Path.join(workspace, "elixir/captured_reply_laws.ex"))
    for law <- ~w(present absent typed_error panic badarg)a, do: assert(apply(module, law, []))

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 8192, maxHeartbeats: 8_000_000]
    ]

    export = Path.join(tmp, "laws.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 5
    check_export(project, export)
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

    proof = Path.join(project, "ReplyNif/Properties.lean")

    for invalid <- [
          nif_properties <> "\nprivate axiom unchecked_reply : False\n",
          nif_properties <> "\nprivate theorem unfinished_reply : True := by sorry\n"
        ] do
      File.write!(proof, invalid)
      assert_raise RuntimeError, ~r/audit failed/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(
      proof,
      String.replace(
        nif_properties,
        "NativeCodec.encode (!guard.value)",
        "NativeCodec.encode guard.value"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(proof, nif_properties)

    base = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(base)
    [before, reply_source] = String.split(original, "pub fn reply(", parts: 2)

    changed =
      before <>
        "pub fn reply(" <> String.replace(reply_source, "*value = !*value;", "*value = *value;")

    refute changed == original
    File.write!(base, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(base, original)

    unsupported = project(tmp, "unsupported")

    rejects =
      Keyword.merge(rust_options,
        lean_project: unsupported,
        module_prefix: "UnsupportedReplies.Extraction",
        build_dir: Path.join(tmp, "unsupported-build"),
        proof_modules: [],
        required_properties: []
      )

    File.write!(
      base,
      original <>
        """

        pub fn heap_reply(accepted: bool) -> Result<Option<Box<bool>>, u8> {
            assert!(accepted);
            Ok(Some(Box::new(true)))
        }
        pub fn borrowed_reply(value: &bool, accepted: bool) -> Result<Option<&bool>, u8> {
            assert!(accepted);
            Ok(Some(value))
        }
        pub struct Dropped(bool);
        impl Drop for Dropped { fn drop(&mut self) { self.0 = !self.0; } }
        pub fn drop_reply(accepted: bool) -> Result<Option<Dropped>, u8> {
            assert!(accepted);
            Ok(Some(Dropped(true)))
        }
        """
    )

    for name <- ~w(heap_reply borrowed_reply drop_reply) do
      assert_raise CompileError, ~r/monomorphic ordinary function.*plain data/, fn ->
        Lynx.Rust.verify!(
          workspace,
          "ownership-base",
          Keyword.put(rejects, :roots, ["ownership_base::" <> name])
        )
      end
    end

    File.write!(base, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end

  defp project(tmp, name) do
    project = Path.join(tmp, name)
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
