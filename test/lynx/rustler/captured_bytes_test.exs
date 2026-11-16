defmodule Lynx.Rustler.CapturedBytesTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RUNTIME_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RUNTIME_DIR for owned byte unwind proofs")

  @tag :tmp_dir
  test "returns owned bytes and preserves borrowed mutation through cross-crate panic cleanup", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock base app nif elixir),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    File.mkdir_p!(Path.join(project, "CapturedBytes"))
    proof = Path.join(project, "CapturedBytes/Properties.lean")
    properties = File.read!(Path.join(@fixture, "CapturedBytesProperties.lean"))
    File.write!(proof, properties)

    rust = [
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      roots: ["ownership_app::checked_bytes"],
      lean_project: project,
      module_prefix: "CapturedBytes.Extraction",
      build_dir: Path.join(tmp, "rust-build"),
      proof_modules: ["CapturedBytes.Properties"],
      required_properties:
        ~w(CapturedBytes.Properties.take_bytes CapturedBytes.Properties.checked_bytes)
    ]

    result = Lynx.Rust.verify!(workspace, "ownership-app", rust)
    assert [%{status: :ok}] = result.reports
    assert length(result.extraction.captured_unwind) == 3

    assert %{global_vectors: true, source: :allocator_preserving_charon} =
             result.verification.allocator_layout

    assert Enum.any?(
             result.verification.structural_drops,
             &(&1.type == "core::result::Result" and &1.implementation_verified == false and
                 String.contains?(&1.label, "Global byte-vector"))
           )

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "ownership-app", rust).reports

    export = Path.join(tmp, "rust.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, rust[:proof_modules])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    check_export(project, export)

    project = Path.join(tmp, "nif-proofs")
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxCapturedBytesFixture")
    )

    nif_properties =
      properties
      |> String.replace("CapturedBytes", "BytesNif")
      |> String.replace(
        "open Aeneas Aeneas.Std Lynx ownership_app",
        "open Aeneas Aeneas.Std Lynx ownership_nif ownership_nif.ownership_app"
      )

    File.mkdir_p!(Path.join(project, "BytesNif"))
    nif_proof = Path.join(project, "BytesNif/Properties.lean")
    File.write!(nif_proof, nif_properties)

    options = [
      workspace: workspace,
      package: "ownership-nif",
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["captured-bytes"]],
      root_attribute: "lynx::captured_bytes",
      only: [captured_bytes: 2],
      lean_project: project,
      module_prefix: "BytesNif.Extraction",
      build_dir: Path.join(tmp, "nif-build"),
      proof_modules: ["BytesNif.Properties"],
      required_properties: ~w(BytesNif.Properties.take_bytes BytesNif.Properties.checked_bytes)
    ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert [%{"name" => "captured_bytes", "arity" => 2, "flags" => 1, "captured_unwind" => true}] =
             prepared.bindings.bindings

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))

    stub =
      File.read!(Path.join(workspace, "elixir/native.ex"))
      |> String.replace("LynxOwnershipFixture", "LynxCapturedBytesFixture")
      |> String.replace(
        "\nend\n",
        "\n  def captured_bytes(_, _), do: :erlang.nif_error(:not_loaded)\nend\n"
      )

    Code.compile_string(stub, Path.join(workspace, "elixir/native.ex"))
    [{module, beam}] = Code.compile_file(Path.join(workspace, "elixir/captured_bytes_laws.ex"))
    for law <- ~w(bytes narrowing empty panic badarg)a, do: assert(apply(module, law, []))

    laws = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 8192, maxHeartbeats: 8_000_000]
    ]

    export = Path.join(tmp, "laws.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(laws, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 5
    check_export(project, export)
    assert Enum.all?(Lynx.Laws.verify([beam], laws), &(&1.status == :ok and &1.cached))

    for invalid <- [
          nif_properties <> "\nprivate axiom unchecked_bytes : False\n",
          nif_properties <> "\nprivate theorem unfinished_bytes : True := by sorry\n"
        ] do
      File.write!(nif_proof, invalid)
      assert_raise RuntimeError, ~r/audit failed/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(nif_proof, nif_properties)
    base = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(base)
    changed = String.replace(original, "require_bytes(accepted);", "require_bytes(!accepted);")
    refute changed == original
    File.write!(base, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "ownership-app", rust)
    end

    File.write!(
      base,
      original <>
        """

        pub fn wide_bytes(input: &mut Vec<u16>, accepted: bool) -> Vec<u16> {
            let original = std::mem::replace(input, Vec::new());
            require_bytes(accepted);
            original
        }
        pub struct OwnedByte(pub u8);
        impl Drop for OwnedByte { fn drop(&mut self) { self.0 = 0; } }
        pub fn custom_bytes(input: &mut Vec<OwnedByte>, accepted: bool) -> Vec<OwnedByte> {
            let original = std::mem::replace(input, Vec::new());
            require_bytes(accepted);
            original
        }
        """
    )

    rejects = Keyword.drop(rust, [:proof_modules, :required_properties])

    for name <- ~w(wide_bytes custom_bytes) do
      assert_raise CompileError, ~r/monomorphic ordinary function.*plain data/, fn ->
        Lynx.Rust.verify!(
          workspace,
          "ownership-base",
          Keyword.put(rejects, :roots, ["ownership_base::" <> name])
        )
      end
    end

    File.write!(
      base,
      "#![feature(allocator_api)]\n" <>
        original <>
        """

        pub fn system_reply(input: Vec<u8, std::alloc::System>, accepted: bool)
            -> Result<Option<Vec<u8, std::alloc::System>>, u8> {
            let reply = Ok(Some(input));
            require_bytes(accepted);
            reply
        }
        """
    )

    assert_raise ArgumentError, ~r/compiler-confirmed Global/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "ownership-base",
        Keyword.put(rejects, :roots, ["ownership_base::system_reply"])
      )
    end

    File.write!(base, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "ownership-app", rust).reports
  end

  defp check_export(project, export) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
