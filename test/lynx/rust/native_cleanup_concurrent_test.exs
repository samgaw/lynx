defmodule Lynx.Rust.NativeCleanupConcurrentTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for concurrent native cleanup proofs")

  @tag :tmp_dir
  test "checks compiler cleanup and unrelated live payloads under every interleaving", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Cleanup"))
    property = Path.join(project, "Cleanup/Properties.lean")
    source = File.read!(Path.join(@fixture, "NativeCleanupConcurrent.lean"))
    File.write!(property, source)

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::mutex_new_incremented", "effects_native::mutex_scope_flag"],
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Cleanup.Extraction",
      proof_modules: ["Cleanup.Properties"],
      required_properties: [
        "Cleanup.Properties.every_interleaving",
        "Cleanup.Properties.every_run"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "effects_native::mutex_new_incremented" &&
               guarantee.theorem == "Cleanup.Properties.every_run"
           end)

    assert result.verification.owned_drops

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "effects_native::mutex_scope_flag" &&
               guarantee.theorem == "Cleanup.Properties.every_run"
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Lynx.Rust.Proofs.file!(
        result.extraction,
        options[:proof_modules]
      )

    export = Path.join(tmp, "cleanup.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    assert File.read!(export) =~ "every_run"
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for invalid <- [
          String.replace(source, "env.nativeHeap.length == 1", "env.nativeHeap.length == 2"),
          source <> "\nprivate axiom uncheckedCleanup : False\n",
          source <> "\nprivate theorem unfinishedCleanup : False := by sorry\n"
        ] do
      refute invalid == source
      File.write!(property, invalid)
      assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "effects-native", options) end
    end

    File.write!(property, source)
    native = Path.join(workspace, "native/src/lib.rs")
    implementation = File.read!(native)

    for broken <- [
          String.replace(
            implementation,
            "let changed = effects_core::increment(&mut counter, amount);",
            "let changed = effects_core::increment(&mut counter, 0);"
          ),
          String.replace(
            implementation,
            "let _mutex = Mutex::new(value);\n    true",
            "true"
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
