defmodule Lynx.Rust.VerificationTest do
  use ExUnit.Case
  @fixture Path.expand("../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "initializes a proof project and reports actual internal and cross-crate properties", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for file <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))

    project = Path.join(workspace, "lynx-proofs")
    File.mkdir_p!(Path.join(project, "Native"))
    # Reuse already installed Lake dependencies when available. Initialization,
    # dependency resolution and the actual proof run remain the production path.
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "Native/Properties.lean"), """
    module
    public import Native.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace Native.Properties
    theorem inverse (value : Bool) : experiment_analysis.experiment_core.invert value = RustM.ok (!value) := by
      cases value <;> rfl
    theorem restore_property (value : Bool) : experiment_analysis.restore value = RustM.ok value := by
      simp only [experiment_analysis.restore, inverse, bind_ok]
      cases value <;> rfl
    theorem unrelated : True := True.intro
    end Native.Properties
    """)

    result =
      Lynx.Rust.verify!(workspace, "experiment-analysis",
        roots: ["experiment_analysis::restore"],
        proof_modules: ["Native.Properties"],
        required_properties: ["Native.Properties.restore_property"],
        build_dir: Path.join(tmp, "build")
      )

    assert result.project == project
    assert File.regular?(Path.join(project, "lakefile.toml"))
    assert File.read!(Path.join(project, "lean-toolchain")) == "leanprover/lean4:v4.35.0\n"

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :rust_implementation && row.theorem == "Native.Properties.inverse" &&
               row.rust_name == "experiment_core::invert"
           end)

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Native.Properties.restore_property" &&
               "Native.Properties.inverse" in row.contracts_used
           end)

    refute Enum.any?(
             result.verification.guarantees,
             &(&1.theorem == "Native.Properties.unrelated")
           )

    assert result.verification.unverified_external_calls == []
    unannotated = Lynx.Rust.Proofs.file!(result.extraction, [])
    unannotated_reports = Lynx.Commands.verify!(project, [unannotated])

    unannotated_evidence =
      Lynx.Rust.Report.build!(result.extraction, unannotated_reports,
        source_dir: result.context.record["directory"]
      )

    assert unannotated_evidence.guarantees == []
    assert Enum.all?(unannotated_evidence.implementations, &(&1.status == :extracted))

    for required <- ["Native.Properties.unrelated", "Native.Properties.missing"] do
      file =
        Lynx.Rust.Proofs.file!(result.extraction, ["Native.Properties"],
          required_properties: [required]
        )

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &(&1.message =~ "required Rust property is missing"))
    end
  end
end
