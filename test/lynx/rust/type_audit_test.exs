defmodule Lynx.Rust.TypeAuditTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_PURE_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR or LYNX_AENEAS_DIR")

  for {kind, package, root} <- [
        {:empty, "experiment-core", "experiment_core::invert"},
        {:typed, "experiment-analysis", "experiment_analysis::classify"}
      ] do
    @tag :tmp_dir
    @tag kind: kind
    test "audits generated #{kind} types with actual Rust implementation proofs", %{
      tmp_dir: tmp,
      kind: kind
    } do
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "TypeAudit"))
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      theorem =
        case kind do
          :empty ->
            """
            theorem implementation (value : Bool) :
                experiment_core.invert value = RustM.ok (!value) := by
              cases value <;> rfl
            """

          :typed ->
            """
            theorem implementation (enabled : Bool) (value : I64) :
                experiment_analysis.classify (enabled, value) =
                  RustM.ok (if enabled then .Ok value else .Err 7#u8) := by
              cases enabled <;>
                simp [experiment_analysis.classify, experiment_analysis.experiment_core.decide]
            """
        end

      File.write!(Path.join(project, "TypeAudit/Properties.lean"), """
      module
      public import TypeAudit.Extraction.Funs
      public section
      open Aeneas Aeneas.Std
      namespace TypeAudit.Properties
      #{theorem}
      end TypeAudit.Properties
      """)

      options = [
        roots: [unquote(root)],
        tools: @tools,
        lean_project: project,
        build_dir: Path.join(tmp, "build"),
        module_prefix: "TypeAudit.Extraction",
        proof_modules: ["TypeAudit.Properties"],
        required_properties: ["TypeAudit.Properties.implementation"]
      ]

      result = Lynx.Rust.verify!(workspace, unquote(package), options)
      assert [%{status: :ok}] = result.reports
      assert "TypeAudit.Extraction.Types" in result.extraction.audit_modules
      if kind == :empty, do: assert(result.extraction.translation["types"] == [])

      file =
        Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
          required_properties: options[:required_properties]
        )

      file = Map.put(file, "cache_key", result.extraction.fingerprint)
      assert "TypeAudit.Extraction.Types" in file["audit_modules"]

      assert_raise KeyError, fn ->
        Lynx.Rust.Proofs.file!(
          Map.delete(result.extraction, :audit_modules),
          options[:proof_modules]
        )
      end

      assert [%{status: :ok, cached: false}] = Lynx.Commands.verify!(project, [file])
      assert [%{status: :ok, cached: true}] = Lynx.Commands.verify!(project, [file])
      export = Path.join(project, "type-audit.export")
      assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
      types = Path.join(project, "TypeAudit/Extraction/Types.lean")
      original = File.read!(types)

      for declaration <- [
            "private axiom unusedTypeTrust : False",
            "private theorem unfinishedType : True := by sorry"
          ] do
        File.write!(types, original <> "\n" <> declaration <> "\n")
        Lynx.Rust.Project.build!(project, ["TypeAudit.Properties"])

        assert [%{status: :error, cached: false, diagnostics: diagnostics}] =
                 Lynx.Commands.verify!(project, [file])

        assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
      end

      File.write!(types, original)
      Lynx.Rust.Project.build!(project, ["TypeAudit.Properties"])
      assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file])
    end
  end
end
