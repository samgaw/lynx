defmodule Lynx.Rust.NativeArcConcurrentTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for concurrent native owner-retention proofs")

  @tag :tmp_dir
  test "retains shared resource payloads under every interleaving", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Retain"))
    property = Path.join(project, "Retain/Properties.lean")
    source = File.read!(Path.join(@fixture, "NativeArcConcurrent.lean"))
    File.write!(property, source)

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::scalar_resource_clone", "effects_native::scalar_resource_read"],
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Retain.Extraction",
      proof_modules: ["Retain.Properties"],
      required_properties: [
        "Retain.Properties.every_interleaving",
        "Retain.Properties.every_run"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "effects_native::scalar_resource_clone" &&
               guarantee.theorem == "Retain.Properties.every_run"
           end)

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :cross_crate_contract &&
               guarantee.rust_name == "effects_native::scalar_resource_read" &&
               guarantee.theorem == "Retain.Properties.every_run"
           end)

    assert result.verification.owned_drops

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "effects_native::scalar_resource_read" &&
               guarantee.theorem == "Retain.Properties.every_run"
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Lynx.Rust.Proofs.file!(
        result.extraction,
        options[:proof_modules]
      )

    export = Path.join(tmp, "retain.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    assert File.read!(export) =~ "every_run"
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for invalid <- [
          String.replace(source, "count == 4", "count == 3"),
          source <> "\nprivate axiom uncheckedRetain : False\n",
          source <> "\nprivate theorem unfinishedRetain : False := by sorry\n"
        ] do
      refute invalid == source
      File.write!(property, invalid)
      assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "effects-native", options) end
    end

    File.write!(property, source)
    native = Path.join(workspace, "native/src/lib.rs")
    implementation = File.read!(native)

    for broken <- [
          String.replace(implementation, "effects_core::counter_value(&resource.counter)", "0"),
          String.replace(
            implementation,
            "-> rustler::ResourceArc<ScalarResource> {\n    resource.clone()\n}",
            "-> rustler::ResourceArc<ScalarResource> {\n    scalar_resource_new(99)\n}"
          )
        ] do
      refute broken == implementation
      File.write!(native, broken)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "effects-native", options)
      end
    end

    File.write!(native, implementation)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end
end
