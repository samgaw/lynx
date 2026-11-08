defmodule Lynx.Rust.NativeAllocationConcurrentTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for concurrent native allocation proofs")

  @tag :tmp_dir
  test "checks distinct allocations and cross-crate payloads under every interleaving", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Allocation"))
    property = Path.join(project, "Allocation/Properties.lean")
    source = File.read!(Path.join(@fixture, "NativeAllocationConcurrent.lean"))
    File.write!(property, source)

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::mutex_new_incremented"],
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Allocation.Extraction",
      proof_modules: ["Allocation.Properties"],
      required_properties: [
        "Allocation.Properties.every_interleaving",
        "Allocation.Properties.every_schedule"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "effects_native::mutex_new_incremented" &&
               guarantee.theorem == "Allocation.Properties.every_interleaving"
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Lynx.Rust.Proofs.file!(
        result.extraction,
        options[:proof_modules]
      )

    export = Path.join(tmp, "allocation.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    assert File.read!(export) =~ "every_interleaving"
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for invalid <- [
          String.replace(source, "11#u64 5#u64 16#u64", "11#u64 5#u64 17#u64"),
          source <> "\nprivate axiom uncheckedAllocation : False\n",
          source <> "\nprivate theorem unfinishedAllocation : False := by sorry\n"
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
        "let changed = effects_core::increment(&mut counter, amount);",
        "let changed = effects_core::increment(&mut counter, 0);"
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
