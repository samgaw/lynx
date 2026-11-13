defmodule Lynx.Rust.NativeFileFinalizationTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "+owned-drops-v1"),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-drops backend")

  @tag :tmp_dir
  test "composes suspended and failed file finalization with actual Rust release", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "FileResource"))
    property = Path.join(project, "FileResource/Finalization.lean")
    source = File.read!(Path.join(@fixture, "NativeFileFinalization.lean"))
    File.write!(property, source)

    File.cp!(
      Path.join(@fixture, "NativeFileResourceModel.lean"),
      Path.join(project, "FileResource/Model.lean")
    )

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::file_resource_release_ack"],
      files: :regular,
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "FileResource.Extraction",
      proof_modules: ["FileResource.Model", "FileResource.Finalization"],
      required_properties:
        Enum.map(
          ~w(suspended_cleanup_interleavings suspended_cleanup_runs close_error_consumes_file missing_close_rejected interrupted_cleanup_retains_state blocked_close_not_completed),
          &("FileResource.Finalization." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "effects_native::file_resource_release_ack" &&
               guarantee.theorem == "FileResource.Finalization.suspended_cleanup_runs"
           end)

    assert result.verification.owned_drops

    assert [%{lean_name: "effects_native.FileResource.drop_owned"}] =
             result.verification.resource_cleanup

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "physical descriptor reclamation")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Lynx.Rust.Proofs.file!(
        result.extraction,
        options[:proof_modules]
      )

    export = Path.join(tmp, "file-finalization.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    assert File.read!(export) =~ "suspended_cleanup_runs"
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for invalid <- [
          String.replace(source, "state.durable.data == #[1]", "state.durable.data == #[2]"),
          String.replace(source, "      | .busy =>", "      | .completed =>"),
          source <> "\nprivate axiom uncheckedFinalization : False\n",
          source <> "\nprivate theorem unfinishedFinalization : False := by sorry\n"
        ] do
      refute invalid == source
      File.write!(property, invalid)
      assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "effects-native", options) end
    end

    File.write!(property, source)
    native = Path.join(workspace, "native/src/lib.rs")
    implementation = File.read!(native)

    broken =
      String.replace(
        implementation,
        "file_resource_release(resource);\n    true",
        "file_resource_release(resource);\n    false"
      )

    refute broken == implementation
    File.write!(native, broken)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(native, implementation)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end
end
