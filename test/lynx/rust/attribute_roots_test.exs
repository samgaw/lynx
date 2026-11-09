defmodule Lynx.Rust.AttributeRootsTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @packages Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for release-binary root selection")

  @tag :tmp_dir
  test "proves an internal nested workspace root without a NIF or path-resolution patch", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    for member <- ~w(core analysis), do: File.mkdir_p!(Path.join([workspace, member, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["core", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "core/Cargo.toml"), """
    [package]
    name = "attribute-core"
    version = "0.1.0"
    edition = "2021"
    """)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "attribute-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    attribute-core = { path = "../core" }
    """)

    core = Path.join(workspace, "core/src/lib.rs")
    File.write!(core, "pub fn invert(value: bool) -> bool { !value }\n")
    analysis = Path.join(workspace, "analysis/src/lib.rs")

    source = """
    #![feature(register_tool)]
    #![register_tool(verify)]
    const _: () = {
        #[verify::start_from]
        fn restore(value: bool) -> bool {
            attribute_core::invert(attribute_core::invert(value))
        }
    };
    """

    File.write!(analysis, source)

    {output, status} =
      System.cmd(
        "cargo",
        ["generate-lockfile", "--manifest-path", Path.join(workspace, "Cargo.toml")],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Attribute"))

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "Attribute/Properties.lean"), """
    module
    public import Attribute.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace Attribute.Properties
    theorem invert (value : Bool) :
        attribute_analysis.attribute_core.invert value = RustM.ok (!value) := by cases value <;> rfl
    theorem restore (value : Bool) : attribute_analysis.«_».restore value = RustM.ok value := by
      cases value <;> simp [attribute_analysis.«_».restore, invert, bind_tc_ok]
    end Attribute.Properties
    """)

    options = [
      roots: ["attribute_analysis::_::restore"],
      root_attribute: "verify::start_from",
      tools: @tools,
      lean_project: project,
      module_prefix: "Attribute.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Attribute.Properties"],
      required_properties: ["Attribute.Properties.invert", "Attribute.Properties.restore"]
    ]

    result = Lynx.Rust.verify!(workspace, "attribute-analysis", options)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "attribute-analysis", options).reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "attribute.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    File.write!(analysis, String.replace(source, "#[verify::start_from]", ""))

    assert_raise ArgumentError, ~r/missing, ambiguous or opaque Rust root/, fn ->
      Lynx.Rust.verify!(workspace, "attribute-analysis", options)
    end

    File.write!(
      analysis,
      String.replace(
        source,
        "attribute_core::invert(attribute_core::invert(value))",
        "attribute_core::invert(value)"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "attribute-analysis", options)
    end

    File.write!(analysis, source)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "attribute-analysis", options).reports
  end
end
