defmodule Lynx.Rust.CompositionTest do
  use ExUnit.Case

  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  test "checks extracted first-party bodies and rejects an incorrect property" do
    {output, status} =
      System.cmd(Path.join(@fixture, "extract.sh"), [],
        env: [
          {"CHARON", Path.join(@tools, "charon")},
          {"AENEAS", Path.join(@tools, "aeneas")},
          {"RUSTUP_TOOLCHAIN", "nightly-2026-09-17"}
        ],
        stderr_to_stdout: true
      )

    assert status == 0, output
    proofs = Path.join(@fixture, "proofs")

    assert %{"has_errors" => false, "translated" => %{"fun_decls" => declarations}} =
             proofs |> Path.join("workspace.llbc") |> File.read!() |> JSON.decode!()

    first_party =
      for %{"item_meta" => %{"name" => [%{"Ident" => [crate, 0]} | _]}} = declaration <-
            declarations,
          crate in ["experiment_core", "experiment_analysis"],
          do: declaration

    assert length(first_party) == 2

    for declaration <- first_party do
      assert %{
               "body" => %{"Structured" => _},
               "signature" => %{"is_unsafe" => false},
               "item_meta" => %{"opacity" => "Transparent"}
             } = declaration
    end

    {output, status} = System.cmd("lake", ["build"], cd: proofs, stderr_to_stdout: true)
    assert status == 0, output

    file = Path.join(proofs, "Incorrect.lean")
    on_exit(fn -> File.rm(file) end)

    File.write!(file, """
    import RustWorkspace.Composition
    open Aeneas Aeneas.Std
    theorem incorrect (value : Bool) :
        experiment_analysis.experiment_core.invert value = RustM.ok value := by
      cases value <;> rfl
    """)

    {output, status} =
      System.cmd("lake", ["env", "lean", file], cd: proofs, stderr_to_stdout: true)

    assert status != 0, output
    assert output =~ "error:"

    File.write!(file, """
    import RustWorkspace.Composition
    open Aeneas Aeneas.Std
    theorem wrong_cross_crate_contract (value : Bool) :
        experiment_analysis.restore value = RustM.ok (!value) := by
      cases value <;> simp [RustWorkspace.restore_spec]
    """)

    {output, status} =
      System.cmd("lake", ["env", "lean", file], cd: proofs, stderr_to_stdout: true)

    assert status != 0, output
    assert output =~ "error:"

    for source <- [
          "theorem unfinished : True := by sorry\n" <>
            "run_cmd LynxTest.ProofAudit.checkDeclaration `unfinished #[]\n",
          "axiom nativeResult : Bool\n" <>
            "theorem unapproved : nativeResult = nativeResult := rfl\n" <>
            "run_cmd LynxTest.ProofAudit.checkDeclaration `unapproved #[]\n"
        ] do
      File.write!(file, "import RustWorkspace.Composition\n" <> source)

      {output, status} =
        System.cmd("lake", ["env", "lean", file], cd: proofs, stderr_to_stdout: true)

      assert status != 0, output
      assert output =~ "unexpected axiom"
    end
  end
end
