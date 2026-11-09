defmodule Lynx.Rust.ScalarSupportTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_PURE_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR or LYNX_AENEAS_DIR")

  @tag :tmp_dir
  test "proves actual saturated arithmetic with downstream lemmas and audits their module", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Scalar"))
    property = Path.join(project, "Scalar/Properties.lean")

    File.write!(property, """
    module
    public import Scalar.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace Scalar.Properties
    theorem increment (value : U64) :
        ∃ result, effects_core.saturating_increment value = RustM.ok result ∧
          result.val = min U64.max (value.val + 1) := by
      refine ⟨core.num.U64.saturating_add value 1#u64, rfl, ?_⟩
      simp
    end Scalar.Properties
    """)

    options = [
      roots: ["effects_core::saturating_increment"],
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Scalar.Extraction",
      proof_modules: ["Scalar.Properties"],
      required_properties: ["Scalar.Properties.increment"]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-core", options)
    assert [%{status: :ok}] = result.reports
    assert "Scalar.NativeScalars" in result.extraction.model_modules

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-core", options).reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(project, "scalar.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    support = Path.join(project, "Scalar/NativeScalars.lean")
    original = File.read!(support)

    for extra <- [
          "private axiom scalarTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(support, original <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["Scalar.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(support, original)
    source = Path.join(workspace, "core/src/lib.rs")
    original_rust = File.read!(source)

    File.write!(
      source,
      String.replace(original_rust, "value.saturating_add(1)", "value.saturating_add(2)")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-core", options)
    end

    File.write!(source, original_rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-core", options).reports
  end
end
