defmodule Lynx.Rust.PromotedTest do
  use ExUnit.Case

  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../fixtures/rust_workspace", __DIR__)
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "proves an actual Rust scalar read through a promoted shared constant", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(Path.join(workspace, "src"))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [package]
    name = "promoted-limits"
    version = "0.1.0"
    edition = "2021"
    """)

    File.write!(Path.join(workspace, "src/lib.rs"), """
    pub const LIMIT: u64 = 4 * 1024;
    pub fn read() -> u64 {
        let reference: &'static u64 = &LIMIT;
        *reference
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
    File.mkdir_p!(Path.join(project, "Promoted"))

    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "Promoted/Properties.lean"), """
    module
    public import Promoted.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    theorem reads_actual_constant : promoted_limits.read ⦃result => result.val = 4096⦄ := by
      unfold promoted_limits.read promoted_limits.LIMIT
      apply WP.spec_mono (UScalar.mul_spec (x := 4#u64) (y := 1024#u64) (by scalar_tac))
      intro result product
      scalar_tac
    """)

    options =
      [
        roots: ["promoted_limits::read"],
        lean_project: project,
        module_prefix: "Promoted.Extraction",
        build_dir: Path.join(tmp, "build"),
        proof_modules: ["Promoted.Properties"],
        required_properties: ["reads_actual_constant"]
      ]

    result = Lynx.Rust.verify!(workspace, "promoted-limits", options)

    assert Enum.any?(result.extraction.audit.constant_initializers, fn initializer ->
             match?(
               %{"Builtin" => ["PromotedConst", _]},
               List.last(initializer["item_meta"]["name"])
             )
           end)

    assert length(result.verification.constants) == 2
    assert Enum.any?(result.verification.constants, &(&1["status"] == :inlined))
    assert result.verification.unverified_external_calls == []

    assert Enum.any?(result.verification.guarantees, fn evidence ->
             evidence.kind == :rust_implementation and
               evidence.theorem == "reads_actual_constant" and
               evidence.rust_name == "promoted_limits::read"
           end)

    # The caller is unchanged: changing the borrowed constant must invalidate
    # the implementation/property correspondence and reject the old property.
    source = Path.join(workspace, "src/lib.rs")
    File.write!(source, String.replace(File.read!(source), "4 * 1024", "5 * 1024"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "promoted-limits", options)
    end
  end
end
