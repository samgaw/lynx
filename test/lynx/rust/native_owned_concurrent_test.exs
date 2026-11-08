defmodule Lynx.Rust.NativeOwnedConcurrentTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for native resource concurrency proofs")

  @tag :tmp_dir
  test "checks resource consumption inside actual cross-crate critical sections for every finite schedule",
       %{
         tmp_dir: tmp
       } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Owned"))

    common =
      File.read!(Path.join(@fixture, "NativeCritical.lean"))
      |> String.replace("Runtime.Critical.Funs", "Owned.Extraction.Funs")
      |> String.replace("Runtime.CriticalProperties", "Owned.Critical")
      |> String.replace("NativeDrop.drop", "NativeOwnedDrop.drop")

    File.write!(Path.join(project, "Owned/Critical.lean"), common)
    property = Path.join(project, "Owned/ResourceConcurrent.lean")
    source = File.read!(Path.join(@fixture, "NativeOwnedConcurrent.lean"))
    File.write!(property, source)

    options = [
      roots: [
        "effects_native::locked_increment_from_resource",
        "effects_native::locked_increment"
      ],
      execution: :runtime,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Owned.Extraction",
      proof_modules: ["Owned.Critical", "Owned.ResourceConcurrent"],
      required_properties: [
        "Owned.Critical.critical_contract",
        "Owned.ResourceConcurrent.worker_wait",
        "Owned.ResourceConcurrent.updates_all_choices"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.theorem == "Owned.ResourceConcurrent.updates_all_choices")
           )

    refute Enum.any?(result.verification.guarantees, &(&1.kind == :nif_adapter))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    export = Path.join(tmp, "owned-concurrent.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    assert File.read!(export) =~ "updates_all_choices"
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for wrong <- [
          String.replace(
            source,
            "shared 9 (pin amount) (free final)) := by",
            "shared 10 (pin amount) (free final)) := by"
          ),
          String.replace(
            source,
            "shared 9 (pin amount) (free final)) := by",
            "shared 9 (both amount) (free final)) := by"
          ),
          String.replace(
            source,
            "shared 9 (pin amount) (free final)) := by",
            "shared 9 (pin amount) (free before)) := by"
          )
        ] do
      refute wrong == source
      File.write!(property, wrong)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "effects-native", options)
        end

      assert error.message =~ "Owned/ResourceConcurrent.lean:"
    end

    for invalid <- [
          "private axiom uncheckedOwnership : False",
          "private theorem unfinishedOwnership : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> invalid <> "\n")

      assert_raise RuntimeError, ~r/Rust properties or proof audit failed/, fn ->
        Lynx.Rust.verify!(workspace, "effects-native", options)
      end
    end

    File.write!(property, source)
    native = Path.join(workspace, "native/src/lib.rs")
    implementation = File.read!(native)

    broken =
      String.replace(
        implementation,
        "let amount = scalar_resource_read(&resource);\n    drop(resource);\n    effects_core::update_release(guard, amount)",
        "let amount = scalar_resource_read(&resource);\n    drop(resource);\n    effects_core::update_release(guard, 0)"
      )

    refute broken == implementation

    try do
      File.write!(native, broken)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "effects-native", options)
        end

      assert error.message =~ "Owned/ResourceConcurrent.lean:"
    after
      File.write!(native, implementation)
    end

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end
end
