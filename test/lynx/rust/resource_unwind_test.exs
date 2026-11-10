defmodule Lynx.Rust.ResourceUnwindTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RESOURCE_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_CAPTURED_RESOURCE_DIR for resource unwind proofs")

  @tag :tmp_dir
  test "verifies an internal resource consumer and final-owner cleanup across crates", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "ResourceInternal"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    property = Path.join(project, "ResourceInternal/Properties.lean")
    proof = File.read!(Path.join(@fixture, "ResourceUnwindInternal.lean"))
    File.write!(property, proof)

    opts = [
      roots: ["ownership_nif::checked_resource_inner"],
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["resource-unwind"]],
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "ResourceInternal.Extraction",
      proof_modules: ["ResourceInternal.Properties"],
      required_properties:
        ~w(ResourceInternal.Properties.mutate ResourceInternal.Properties.checked ResourceInternal.Properties.inner ResourceInternal.Properties.inner_final)
    ]

    verify = fn -> Lynx.Rust.verify!(workspace, "ownership-nif", opts) end
    result = verify.()
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))
    refute Enum.any?(result.verification.guarantees, &(&1.kind == :nif_adapter))
    assert Enum.any?(result.extraction.native_drops, & &1.unwind)
    assert [%{status: :ok, cached: true}] = verify.().reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, opts[:proof_modules],
        required_properties: opts[:required_properties]
      )

    export = Path.join(tmp, "resource-internal.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    raw = result.extraction.llbc |> File.read!() |> JSON.decode!()

    missing =
      update_in(raw, ["translated", "type_decls"], fn types ->
        Enum.map(types, fn type -> if type, do: Map.delete(type, "needs_drop") end)
      end)

    assert_raise CompileError,
                 ~r/unsupported resource destructor, payload or Resource callbacks/,
                 fn ->
                   Lynx.Rust.NativeDropLowering.lower!(
                     missing,
                     result.extraction.audit.first_party,
                     unwind: :captured
                   )
                 end

    for extra <- [
          "private axiom resourceTrust : False",
          "private theorem unfinishedResource : True := by sorry"
        ] do
      File.write!(property, proof <> "\n" <> extra)
      assert_raise RuntimeError, ~r/Rust properties or proof audit failed/, verify
    end

    File.write!(property, proof)
    wrong = String.replace(proof, "core.result.Result.Ok (!value)", "core.result.Result.Ok value")
    refute wrong == proof
    File.write!(property, wrong)
    assert_raise RuntimeError, ~r/native Lean project command failed/, verify
    File.write!(property, proof)

    source = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(source)
    File.write!(source, String.replace(original, "*value = !*value;", "*value = *value;"))
    assert_raise RuntimeError, ~r/native Lean project command failed/, verify
    File.write!(source, original)
    assert [%{status: :ok}] = verify.().reports

    native = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      native,
      File.read!(native) <>
        "\n#[cfg(feature = \"resource-unwind\")]\nimpl Drop for UnwindResource { fn drop(&mut self) {} }\n"
    )

    assert_raise CompileError,
                 ~r/unsupported resource destructor, payload or Resource callbacks/,
                 verify
  end
end
