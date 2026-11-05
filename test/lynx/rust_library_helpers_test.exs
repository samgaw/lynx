defmodule Lynx.Rust.LibraryHelpersTest do
  use ExUnit.Case
  alias Lynx.Rust.LLBC

  @tools System.get_env("LYNX_AENEAS_DIR")
  @packages Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "retains actual display helpers from distinct dependency versions", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    for name <- ~w(base analysis), do: File.mkdir_p!(Path.join([workspace, name, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["base", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "base/Cargo.toml"), """
    [package]
    name = "library-base"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    thiserror-v1 = { package = "thiserror", version = "=1.0.69" }
    thiserror-v2 = { package = "thiserror", version = "=2.0.18" }
    """)

    source = Path.join(workspace, "base/src/lib.rs")

    original = """
    pub fn via_v1(value: u64) -> u64 {
        use thiserror_v1::__private::AsDisplay;
        let reference = &value;
        *reference.as_display()
    }
    pub fn via_v2(value: u64) -> u64 {
        use thiserror_v2::__private18::AsDisplay;
        let reference = &value;
        *reference.as_display()
    }
    """

    File.write!(source, original)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "library-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    library-base = { path = "../base" }
    """)

    File.write!(Path.join(workspace, "analysis/src/lib.rs"), """
    pub fn compose(value: u64) -> u64 {
        library_base::via_v2(library_base::via_v1(value))
    }
    """)

    {output, status} =
      System.cmd(
        "cargo",
        ["generate-lockfile", "--manifest-path", Path.join(workspace, "Cargo.toml")],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "LibraryProofs"))

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "LibraryProofs/Properties.lean"), """
    module
    public import LibraryProofs.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace LibraryProofs
    theorem helper_v1_spec {T : Type} (inst : core.fmt.Display T) (value : T) :
        library_analysis.Shared0T.Insts.ThiserrorDisplayAsDisplayASharedAT.as_display inst value =
          RustM.ok value := by rfl
    theorem helper_v2_spec {T : Type} (inst : core.fmt.Display T) (value : T) :
        library_analysis.Shared0T.Insts.Thiserror_1DisplayAsDisplayASharedAT.as_display inst value =
          RustM.ok value := by rfl
    theorem v1_spec (value : U64) : library_analysis.library_base.via_v1 value = RustM.ok value := by
      simp [library_analysis.library_base.via_v1, helper_v1_spec]
    theorem v2_spec (value : U64) : library_analysis.library_base.via_v2 value = RustM.ok value := by
      simp [library_analysis.library_base.via_v2, helper_v2_spec]
    theorem compose_spec (value : U64) : library_analysis.compose value = RustM.ok value := by
      simp [library_analysis.compose, v1_spec, v2_spec]
    end LibraryProofs
    """)

    result =
      Lynx.Rust.verify!(workspace, "library-analysis",
        roots: ["library_analysis::compose"],
        module_prefix: "LibraryProofs.Extraction",
        lean_project: project,
        build_dir: Path.join(tmp, "build"),
        proof_modules: ["LibraryProofs.Properties"],
        required_properties: [
          "LibraryProofs.helper_v1_spec",
          "LibraryProofs.helper_v2_spec",
          "LibraryProofs.compose_spec"
        ]
      )

    assert [%{status: :ok}] = result.reports

    helpers =
      Enum.filter(
        result.verification.implementations,
        &(&1.source_kind == :included_library_helper)
      )

    assert length(helpers) == 2
    assert Enum.any?(helpers, &String.starts_with?(&1.rust_name, "thiserror::"))
    assert Enum.any?(helpers, &String.starts_with?(&1.rust_name, "thiserror#1::"))
    assert result.verification.unverified_external_calls == []

    for row <- helpers do
      theorem =
        if String.starts_with?(row.rust_name, "thiserror#1::"),
          do: "LibraryProofs.helper_v2_spec",
          else: "LibraryProofs.helper_v1_spec"

      assert Enum.any?(result.verification.guarantees, fn guarantee ->
               guarantee.rust_name == row.rust_name and guarantee.kind == :rust_implementation and
                 guarantee.source_kind == :included_library_helper and
                 guarantee.theorem == theorem
             end)
    end

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract and row.theorem == "LibraryProofs.v1_spec" and
               "LibraryProofs.helper_v1_spec" in row.contracts_used
           end)

    export = Path.join(tmp, "library-helpers.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["LibraryProofs.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    document = JSON.decode!(File.read!(result.extraction.llbc))
    [helper | _] = result.extraction.audit.library_helpers
    declaration = Enum.find(document["translated"]["fun_decls"], &(&1 && &1["def_id"] == helper))
    impl = get_in(declaration, ["src", "TraitImpl", "impl_ref", "id"])
    trait = get_in(declaration, ["src", "TraitImpl", "trait_ref", "id"])

    for invalid <- [
          change(document, "fun_decls", helper, &put_in(&1, ["body"], "Opaque")),
          change(document, "fun_decls", helper, &put_in(&1, ["signature", "is_unsafe"], true)),
          change(
            document,
            "fun_decls",
            helper,
            &put_in(&1, ["item_meta", "name", Access.at(1)], %{"Ident" => ["other", 0]})
          ),
          change(
            document,
            "fun_decls",
            helper,
            &put_in(&1, ["src", "TraitImpl", "trait_ref", "id"], -1)
          ),
          change(
            document,
            "trait_impls",
            impl,
            &put_in(&1, ["methods", Access.at(0), "skip_binder", "id"], -1)
          ),
          change(
            document,
            "trait_decls",
            trait,
            &put_in(&1, ["item_meta", "name", Access.at(0)], %{"Ident" => ["thiserror", 9]})
          ),
          change(document, "fun_decls", helper, fn f ->
            update_in(
              f,
              ["body", "Structured", "body", "statements"],
              &[
                %{
                  "kind" => %{
                    "Call" => %{
                      "call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => 999}}}}
                    }
                  }
                }
                | &1
              ]
            )
          end)
        ] do
      assert_raise CompileError, fn ->
        LLBC.audit!(invalid, ["library_base", "library_analysis"])
      end
    end

    missing =
      update_in(
        document,
        ["translated", "fun_decls"],
        &Enum.reject(&1, fn f -> f && f["def_id"] == helper end)
      )

    assert_raise CompileError, fn ->
      LLBC.audit!(missing, ["library_base", "library_analysis"])
    end

    # A correct dependency contract cannot make an incorrect workspace caller pass.
    File.write!(
      source,
      String.replace(original, "*reference.as_display()", "*reference.as_display() + 1")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "library-analysis",
        roots: ["library_analysis::compose"],
        module_prefix: "LibraryProofs.Extraction",
        lean_project: project,
        build_dir: Path.join(tmp, "build"),
        proof_modules: ["LibraryProofs.Properties"],
        required_properties: ["LibraryProofs.compose_spec"]
      )
    end
  end

  defp change(document, kind, id, fun),
    do:
      update_in(
        document,
        ["translated", kind],
        &Enum.map(&1, fn
          %{"def_id" => ^id} = item -> fun.(item)
          item -> item
        end)
      )
end
