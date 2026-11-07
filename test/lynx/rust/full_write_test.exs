defmodule Lynx.Rust.FullWriteTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "native-loops-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native-loops backend")

  @tag :tmp_dir
  test "recovers full writes without inventing or losing acknowledged payloads", %{tmp_dir: tmp} do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, ["CompleteRecovery", "FullWriteConcurrent"])

    properties = [
      "Record.CompleteRecovery.repair_append_image",
      "Record.FullWriteConcurrent.full_write_stalls",
      "Record.FullWriteConcurrent.full_write_crash_repair",
      "Record.FullWriteConcurrent.surviving_full_record"
    ]

    options = base ++ [required_properties: properties]
    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.FullWriteConcurrent.full_write_crash_repair")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "full-write.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for module <- ~w(CompleteRecovery FullWriteConcurrent) do
      path = Path.join(project, "Record/#{module}.lean")
      source = File.read!(path)

      for extra <- [
            "private axiom trustFullWrite : False",
            "private theorem unfinishedFullWrite : True := by sorry"
          ] do
        File.write!(path, source <> "\n" <> extra <> "\n")
        Project.build!(project, options[:proof_modules])
        assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
        File.write!(path, source)
      end
    end

    path = Path.join(project, "Record/CompleteRecovery.lean")
    source = File.read!(path)

    native =
      Regex.replace(
        ~r/    rw \[found\] at bits\n.*?(?=  have first :)/s,
        source,
        "    bv_decide\n"
      )

    refute native == source
    File.write!(path, native)
    Project.build!(project, options[:proof_modules])
    assert [%{status: :error, diagnostics: diagnostics}] = Lynx.Commands.verify!(project, [file])
    assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    File.write!(path, source)

    for module <- ~w(CompleteRecovery FullWriteConcurrent) do
      path = Path.join(project, "Record/#{module}.lean")
      source = File.read!(path)

      wrong =
        String.replace(
          source,
          "(recovered.val = values ∨ recovered.val = values ++ [value])",
          "(recovered.val = values)"
        )

      refute wrong == source
      File.write!(path, wrong)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Project.build!(project, options[:proof_modules])
        end

      assert error.message =~ "Record/#{module}.lean:"
      File.write!(path, source)
    end

    path = Path.join(project, "Record/FullWriteConcurrent.lean")
    source = File.read!(path)

    wrong =
      String.replace(
        source,
        "some (alloc.vec.Vec.from [value] (by scalar_tac))",
        "some (alloc.vec.Vec.from [] (by scalar_tac))"
      )

    refute wrong == source
    File.write!(path, wrong)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Project.build!(project, options[:proof_modules])
      end

    assert error.message =~ "Record/FullWriteConcurrent.lean:"
    File.write!(path, source)

    protocol = Path.join(workspace, "protocol/src/lib.rs")
    original = File.read!(protocol)
    broken = String.replace(original, "Ok(()) => Ok(true),", "Ok(()) => Ok(false),")
    refute broken == original
    File.write!(protocol, broken)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Record/RollbackProperties.lean:"
    File.write!(protocol, original)

    core = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(core)

    broken =
      String.replace(
        original,
        "let [low, high] = value.to_le_bytes();",
        "let [low, high] = 0u16.to_le_bytes();"
      )

    refute broken == original
    File.write!(core, broken)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Record/IntegrityProperties.lean:"
    File.write!(core, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
