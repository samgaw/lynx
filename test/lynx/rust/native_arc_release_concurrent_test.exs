defmodule Lynx.Rust.NativeArcReleaseConcurrentTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for concurrent native owner-release proofs")

  @tag :tmp_dir
  test "releases owners and dispatches final cleanup under every interleaving", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Reclaim"))
    property = Path.join(project, "Reclaim/Properties.lean")
    source = File.read!(Path.join(@fixture, "NativeArcReleaseConcurrent.lean"))
    File.write!(property, source)

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::resource_release_ack"],
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Reclaim.Extraction",
      proof_modules: ["Reclaim.Properties"],
      required_properties: [
        "Reclaim.Properties.deferred_interleavings",
        "Reclaim.Properties.deferred_schedules",
        "Reclaim.Properties.repeated_owner_rejected",
        "Reclaim.Properties.synchronous_interleavings",
        "Reclaim.Properties.synchronous_schedules",
        "Reclaim.Properties.release_can_precede_cleanup",
        "Reclaim.Properties.missing_policy_rejected"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "effects_native::resource_release_ack" &&
               guarantee.theorem == "Reclaim.Properties.deferred_interleavings"
           end)

    assert result.verification.owned_drops

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Lynx.Rust.Proofs.file!(
        result.extraction,
        options[:proof_modules]
      )

    export = Path.join(tmp, "release.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    assert File.read!(export) =~ "deferred_interleavings"
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for invalid <- [
          String.replace(source, "payload == 17", "payload == 18"),
          String.replace(source, "(.start (initial .synchronous)", "(.start (initial .deferred)"),
          source <> "\nprivate axiom uncheckedReclaim : False\n",
          source <> "\nprivate theorem unfinishedReclaim : False := by sorry\n"
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
        "resource_release(resource);\n    true",
        "resource_release(resource);\n    false"
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
