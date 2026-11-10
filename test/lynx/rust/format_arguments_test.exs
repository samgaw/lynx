defmodule Lynx.Rust.FormatArgumentsTest do
  use ExUnit.Case
  alias Lynx.Rust.LLBC

  @tools System.get_env("LYNX_AENEAS_DIR")
  @packages Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "format arguments invoke the audited scalar renderer across crates", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    for name <- ~w(base analysis), do: File.mkdir_p!(Path.join([workspace, name, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["base", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "base/Cargo.toml"), """
    [package]
    name = "argument-base"
    version = "0.1.0"
    edition = "2021"
    """)

    source = Path.join(workspace, "base/src/lib.rs")

    original = """
    pub struct Count(pub u64);
    impl std::fmt::Display for Count {
        #[expect(
            clippy::useless_borrows_in_formatting,
            reason = "Exercise the shared-reference Display dictionary"
        )]
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "n={}", &self.0)
        }
    }
    pub struct Rejected(pub u64);
    impl std::fmt::Display for Rejected {
        fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            Err(std::fmt::Error)
        }
    }
    """

    File.write!(source, original)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "argument-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    argument-base = { path = "../base" }
    """)

    File.write!(Path.join(workspace, "analysis/src/lib.rs"), """
    pub fn describe(value: u64) -> String {
        argument_base::Count(value).to_string()
    }
    pub fn formatted(value: u64) -> String {
        format!("{}", argument_base::Count(value))
    }
    pub fn rejected(value: u64) -> String {
        format!("{}", argument_base::Rejected(value))
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
    File.mkdir_p!(Path.join(project, "Arguments"))

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    File.cp!(
      Path.expand("../../fixtures/rust_format_arguments/Properties.lean", __DIR__),
      Path.join(project, "Arguments/Properties.lean")
    )

    options = [
      roots: [
        "argument_analysis::describe",
        "argument_analysis::formatted",
        "argument_analysis::rejected"
      ],
      mir: :elaborated,
      lean_project: project,
      module_prefix: "Arguments.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Arguments.Properties"],
      required_properties: [
        "Arguments.renderer_spec",
        "Arguments.describe_spec",
        "Arguments.zero_spec",
        "Arguments.formatted_spec",
        "Arguments.rejected_spec"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "argument-analysis", options)

    calls = result.verification.unverified_external_calls
    assert length(calls) == 7
    assert Enum.all?(calls, &(&1.status == :modelled and not &1.implementation_verified))
    assert Enum.any?(calls, &String.contains?(&1.rust_name, "Display<u64>"))

    for theorem <- ["Arguments.describe_spec", "Arguments.formatted_spec"] do
      assert Enum.any?(result.verification.guarantees, fn row ->
               row.kind == :cross_crate_contract and row.theorem == theorem and
                 "Arguments.renderer_spec" in row.contracts_used
             end)
    end

    assert "Arguments.NativeFormatting" in result.extraction.audit_modules

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "argument-analysis", options).reports

    document = JSON.decode!(File.read!(result.extraction.llbc))

    for model <- Map.values(result.extraction.audit.external_calls) do
      broken =
        update_in(document, ["translated", "fun_decls"], fn functions ->
          Enum.map(functions, fn
            %{"def_id" => id} = function when id == model.definition_id ->
              put_in(function, ["signature", "abi"], "C")

            function ->
              function
          end)
        end)

      assert_raise CompileError, fn ->
        LLBC.audit!(broken, ["argument_base", "argument_analysis"])
      end
    end

    helper =
      Enum.find(
        result.extraction.audit.functions,
        &(&1["item_meta"]["name"] ==
            Enum.map(~w(core hint must_use), fn part -> %{"Ident" => [part, 0]} end))
      )

    assert helper["def_id"] in result.extraction.audit.library_helpers
    assert is_map(helper["body"])

    opaque_helper =
      update_in(document, ["translated", "fun_decls"], fn functions ->
        Enum.map(functions, fn f ->
          if f && f["def_id"] == helper["def_id"], do: %{f | "body" => "Opaque"}, else: f
        end)
      end)

    assert_raise CompileError, ~r/missing or unsupported first-party implementation/, fn ->
      LLBC.audit!(opaque_helper, ["argument_base", "argument_analysis"])
    end

    export = Path.join(tmp, "display.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["Arguments.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    model_path = Path.join(project, "Arguments/NativeFormatting.lean")
    model_source = File.read!(model_path)

    for extra <- [
          "private axiom formattingTrust : False",
          "private theorem unfinishedFormatting : True := by sorry"
        ] do
      File.write!(model_path, model_source <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["Arguments.Properties"])
      assert [%{status: :error, cached: false}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(model_path, model_source)
    Lynx.Rust.Project.build!(project, ["Arguments.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file])

    # The old theorem must fail when the real Rust formatter changes.
    File.write!(source, String.replace(original, "n={}", "m={}"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "argument-analysis", options)
    end

    File.write!(source, String.replace(original, "n={}", "n={:?}"))

    assert_raise CompileError, fn ->
      Lynx.Rust.verify!(workspace, "argument-analysis", options)
    end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "argument-analysis", options).reports
  end
end
