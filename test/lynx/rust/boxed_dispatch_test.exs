defmodule Lynx.Rust.BoxedDispatchTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @packages Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for boxed implementation proofs")

  @tag :tmp_dir
  test "proves the implementation dictionary of a cross-crate boxed value", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    for member <- ~w(core analysis), do: File.mkdir_p!(Path.join([workspace, member, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["core", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "core/Cargo.toml"), """
    [package]
    name = "boxed-core"
    version = "0.1.0"
    edition = "2021"
    """)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "boxed-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    boxed-core = { path = "../core" }
    """)

    source = """
    pub trait Encode { fn encode(&self) -> bool; }
    pub struct Payload { value: bool }
    impl Encode for Payload { fn encode(&self) -> bool { !self.value } }
    pub fn make(value: bool) -> Box<dyn Encode> { Box::new(Payload { value }) }
    """

    core = Path.join(workspace, "core/src/lib.rs")
    File.write!(core, source)

    File.write!(Path.join(workspace, "analysis/src/lib.rs"), """
    #![feature(register_tool)]
    #![register_tool(verify)]
    #[verify::start_from]
    pub fn prepare(value: bool) -> Box<dyn boxed_core::Encode> { boxed_core::make(value) }
    """)

    {output, status} =
      System.cmd(
        "cargo",
        ["generate-lockfile", "--manifest-path", Path.join(workspace, "Cargo.toml"), "--offline"],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Boxed"))

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["boxed_analysis::prepare"],
      root_attribute: "verify::start_from",
      mir: :elaborated,
      tools: @tools,
      lean_project: project,
      module_prefix: "Boxed.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    initial = Lynx.Rust.verify!(workspace, "boxed-analysis", options)
    functions = Map.values(initial.extraction.implementations)
    maker = Enum.find(functions, &(&1["rust_name"] == "boxed_core::make"))["lean_name"]
    root = Enum.find(functions, &(&1["rust_name"] == "boxed_analysis::prepare"))["lean_name"]
    encoder = Enum.find(functions, &String.ends_with?(&1["rust_name"], "::encode"))["lean_name"]

    payload =
      Enum.find(
        initial.extraction.translation["types"],
        &(&1["rust_name"] == "boxed_core::Payload")
      )["lean_name"]

    properties = """
    module
    public import Boxed.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace Boxed.Properties
    theorem encoder_spec (input : #{payload}) : #{encoder} input = RustM.ok (!input.value) := by
      simp [#{encoder}]
    theorem maker_spec (value : Bool) :
        (do let boxed ← #{maker} value
            boxed.inst.encode boxed.value) = RustM.ok (!value) := by
      simp [#{maker}, bind_tc_ok, encoder_spec]
    theorem prepared_spec (value : Bool) :
        (do let boxed ← #{root} value
            boxed.inst.encode boxed.value) = RustM.ok (!value) := by
      simpa [#{root}] using maker_spec value
    end Boxed.Properties
    """

    property = Path.join(project, "Boxed/Properties.lean")
    File.write!(property, properties)

    options =
      options ++
        [
          proof_modules: ["Boxed.Properties"],
          required_properties:
            Enum.map(~w(encoder_spec maker_spec prepared_spec), &("Boxed.Properties." <> &1))
        ]

    verified = Lynx.Rust.verify!(workspace, "boxed-analysis", options)
    assert Enum.all?(verified.reports, &(&1.status == :ok))
    assert Enum.any?(verified.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(verified.verification.external_models, &String.contains?(&1, "vtable ABI"))
    assert Enum.all?(Lynx.Rust.verify!(workspace, "boxed-analysis", options).reports, & &1.cached)

    file =
      Lynx.Rust.Proofs.file!(verified.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "boxed.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom boxedTrust : False",
          "private theorem unfinishedBox : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/audit/, fn ->
        Lynx.Rust.verify!(workspace, "boxed-analysis", options)
      end
    end

    File.write!(property, properties)
    File.write!(core, String.replace(source, "!self.value", "self.value"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "boxed-analysis", options)
    end

    File.write!(core, source)

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "boxed-analysis", options).reports,
             &(&1.status == :ok)
           )
  end
end
