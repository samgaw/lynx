defmodule Lynx.Rust.FormatArgumentsTest do
  use ExUnit.Case
  alias Lynx.Rust.LLBC

  @tools System.get_env("LYNX_AENEAS_DIR")
  @packages Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
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
        #[expect(clippy::useless_borrows_in_formatting, reason = "Exercise the shared-reference Display dictionary")]
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "n={}", &self.0)
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
    pub fn describe(value: u64) -> String { argument_base::Count(value).to_string() }
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
      Path.expand("../fixtures/rust_format_arguments/Properties.lean", __DIR__),
      Path.join(project, "Arguments/Properties.lean")
    )

    options = [
      roots: ["argument_analysis::describe"],
      lean_project: project,
      module_prefix: "Arguments.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Arguments.Properties"],
      required_properties: [
        "Arguments.renderer_spec",
        "Arguments.describe_spec",
        "Arguments.zero_spec"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "argument-analysis", options)

    calls = result.verification.unverified_external_calls
    assert length(calls) == 6
    assert Enum.all?(calls, &(&1.status == :modelled and not &1.implementation_verified))
    assert Enum.any?(calls, &String.contains?(&1.rust_name, "Display<u64>"))

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract and row.theorem == "Arguments.describe_spec" and
               "Arguments.renderer_spec" in row.contracts_used
           end)

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

    export = Path.join(tmp, "display.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["Arguments.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    # The old theorem must fail when the real Rust formatter changes.
    File.write!(source, String.replace(original, "n={}", "m={}"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "argument-analysis", options)
    end

    File.write!(source, String.replace(original, "n={}", "n={:?}"))

    assert_raise CompileError, fn ->
      Lynx.Rust.verify!(workspace, "argument-analysis", options)
    end
  end
end
