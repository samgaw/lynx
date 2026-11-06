defmodule Lynx.Rust.ResourceTest do
  use ExUnit.Case
  @fixture Path.expand("../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "global-names-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned resource/global-names backend")

  @tag :tmp_dir
  test "verifies extracted resource aliasing, final destruction and cross-crate reads", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Resource"))
    packages = Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    property = Path.join(project, "Resource/Properties.lean")
    File.cp!(Path.join(@fixture, "NativeResource.lean"), property)

    opts = [
      roots:
        Enum.map(~w(scalar_resource_cycle scalar_resource_scope), &("effects_native::" <> &1)),
      tools: @tools,
      execution: :runtime,
      lean_project: project,
      module_prefix: "Resource.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Resource.Properties"],
      required_properties:
        Enum.map(
          ~w(counter_reader resource_reader retained_value scope_value unregistered_panics),
          &("Resource.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", opts)
    assert [%{status: :ok}] = result.reports
    assert length(result.verification.properties) == 5
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(result.extraction.native_drops, &(&1[:destructor] != nil))
    assert Enum.any?(result.verification.external_models, &String.contains?(&1, "ResourceArc"))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", opts).reports

    generated = File.read!(Path.join(project, "Resource/Extraction/Funs.lean"))
    refute String.contains?(generated, "FunsExternal")
    assert String.contains?(generated, "Lynx.NativeResourceArc.defaultDestructor")
    assert String.contains?(generated, "Lynx.NativeResourceArc.defaultDown")

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Resource.Properties"])
    export = Path.join(tmp, "resource.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    original = File.read!(property)
    File.write!(property, String.replace(original, "env.refCounter + 3", "env.refCounter + 2"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Resource.Properties"])
    end

    File.write!(
      property,
      String.replace(original, "Result.ok counter.value", "Result.ok 0", global: false)
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Resource.Properties"])
    end

    for extra <- [
          "private axiom resourceTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["Resource.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(property, original)

    # Model preconditions do not establish correspondence to a compiled loader.
    assert_raise ArgumentError, ~r/resource calls require compiled loader registration/, fn ->
      Lynx.Rustler.prepare!(workspace, "effects-native",
        tools: @tools,
        execution: :runtime,
        lean_project: project,
        module_prefix: "Resource.Facade",
        build_dir: Path.join(tmp, "nif-build"),
        cargo: [features: ["resource-nif"]],
        only: [retained: 1]
      )
    end

    core = Path.join(workspace, "core/src/lib.rs")
    source = File.read!(core)

    changed =
      String.replace(source, "    counter.value\n}", "    counter.value ^ 1\n}", global: false)

    refute changed == source
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", opts)
    end

    File.write!(
      core,
      source <> "\nimpl Drop for Counter { fn drop(&mut self) { assert!(false); } }\n"
    )

    assert_raise CompileError, ~r/resource|native destruction|structural drop/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", opts)
    end

    File.write!(core, source)
    native = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      native,
      String.replace(
        File.read!(native),
        "impl rustler::Resource for ScalarResource {}",
        "impl rustler::Resource for ScalarResource { fn destructor(self, _env: rustler::Env<'_>) {} }"
      )
    )

    assert_raise CompileError, ~r/resource|native destruction|structural drop/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", opts)
    end
  end
end
