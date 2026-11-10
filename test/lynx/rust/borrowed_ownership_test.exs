defmodule Lynx.Rust.BorrowedOwnershipTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for borrowed guard proofs")

  @tag :tmp_dir
  test "proves actual cross-crate guard mutation through a mutable borrow", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Borrowed"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.mkdir_p!(Path.join(project, ".lake"))
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    property = Path.join(project, "Borrowed/Properties.lean")
    properties = File.read!(Path.join(@fixture, "BorrowedProperties.lean"))
    File.write!(property, properties)

    options = [
      roots: ["ownership_app::scoped_flip"],
      owned_drops: :explicit,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Borrowed.Extraction",
      proof_modules: ["Borrowed.Properties"],
      required_properties: [
        "Borrowed.Properties.flip_contract",
        "Borrowed.Properties.scoped_flip"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "ownership-app", options)
    assert [%{status: :ok}] = result.reports
    assert [%{local: _, source: _}] = result.extraction.explicit_ownership.reference_copies
    assert result.verification.compiler_primitives == []
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "ownership-app", options).reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "borrowed.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom borrowedTrust : False",
          "private theorem unfinishedBorrow : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/Rust properties or proof audit failed/, fn ->
        Lynx.Rust.verify!(workspace, "ownership-app", options)
      end
    end

    File.write!(property, properties)
    source = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(source)
    changed = String.replace(original, "*self.0 = !*self.0;", "*self.0 = *self.0;")
    refute changed == original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "ownership-app", options)
    end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "ownership-app", options).reports

    # The Aeneas preset reconstructs this assertion and erases the actual
    # destructor cleanup on failure. An empty reconstructed edge is not evidence
    # that unwinding leaves the borrowed flag unchanged.
    changed =
      String.replace(
        original,
        "let _guard = Flip(value);",
        "let _guard = Flip(value); assert!(false);"
      )

    refute changed == original
    File.write!(source, changed)

    assert_raise CompileError, ~r/reconstructed assertions with owned locals/, fn ->
      Lynx.Rust.verify!(workspace, "ownership-app", options)
    end
  end
end
