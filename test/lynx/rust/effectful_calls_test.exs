defmodule Lynx.Rust.EffectfulCallsTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(
             File.read!(Path.join(@tools, "lynx-toolchain")),
             "+effectful-calls-v1"
           ),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned effectful-calls backend")

  @tag :tmp_dir
  test "repeated and discarded calls retain their actual state changes", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "EffectCalls"))

    for {source, target} <- [
          {"NativeEffectCallsCore.lean", "Core"},
          {"NativeEffectCalls.lean", "Properties"}
        ],
        do:
          File.cp!(Path.join(@fixture, source), Path.join(project, "EffectCalls/#{target}.lean"))

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      ["EffectCalls.Core.increment_spec", "EffectCalls.Core.critical_state_next"] ++
        Enum.map(
          ~w(distinct_allocations discarded_effect discarded_state),
          &("EffectCalls.Properties." <> &1)
        )

    options = [
      roots: ["effects_native::identical_mutexes", "effects_native::discarded_update"],
      execution: :runtime,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      module_prefix: "EffectCalls.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["EffectCalls.Core", "EffectCalls.Properties"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports
    assert %{"effectful_calls_preserved" => true} = result.extraction.translation

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "effectful.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for module <- ~w(Core Properties) do
      path = Path.join(project, "EffectCalls/#{module}.lean")
      original = File.read!(path)

      for extra <- [
            "private axiom effectTrust : False",
            "private theorem unfinishedEffect : True := by sorry"
          ] do
        File.write!(path, original <> "\n" <> extra <> "\n")
        Project.build!(project, options[:proof_modules])
        assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      end

      File.write!(path, original)
    end

    property = Path.join(project, "EffectCalls/Properties.lean")
    source = File.read!(property)

    # The incorrect single-update result must fail, even though the first return value is discarded.
    wrong = String.replace(source, "(.ok true, state 2#u64 3)", "(.ok true, state 1#u64 2)")
    refute wrong == source
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, source)

    native = Path.join(workspace, "native/src/lib.rs")
    rust = File.read!(native)

    changed =
      String.replace(rust, "    let _ = effects_core::locked_increment(mutex, amount);\n", "")

    refute changed == rust
    File.write!(native, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "effects-native", options)
      end

    assert error.message =~ "EffectCalls/Properties.lean:"
    File.write!(native, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end
end
