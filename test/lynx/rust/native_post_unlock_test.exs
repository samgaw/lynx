defmodule Lynx.Rust.NativePostUnlockTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "+owned-drops-v1"),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-drops backend")

  @tag :tmp_dir
  test "composes complete cross-crate critical sections with post-unlock owner release", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Tail"))
    property = Path.join(project, "Tail/PostUnlock.lean")
    source = File.read!(Path.join(@fixture, "NativePostUnlock.lean"))
    File.write!(property, source)

    common =
      File.read!(Path.join(@fixture, "NativeCritical.lean"))
      |> String.replace("Runtime.Critical.Funs", "Tail.Extraction.Funs")
      |> String.replace("Runtime.CriticalProperties", "Tail.Critical")
      |> String.replace("NativeDrop.drop", "NativeOwnedDrop.drop")

    File.write!(Path.join(project, "Tail/Critical.lean"), common)

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: [
        "effects_native::locked_increment_then_release_resource",
        "effects_native::locked_increment"
      ],
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Tail.Extraction",
      proof_modules: ["Tail.Critical", "Tail.PostUnlock"],
      required_properties: [
        "Tail.Critical.increment_spec",
        "Tail.Critical.critical_contract",
        "Tail.PostUnlock.composed_contract",
        "Tail.PostUnlock.all_interleavings",
        "Tail.PostUnlock.all_choices",
        "Tail.PostUnlock.overflow_interleavings",
        "Tail.PostUnlock.overflow_choices"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "effects_native::locked_increment_then_release_resource" &&
               guarantee.theorem == "Tail.PostUnlock.all_interleavings"
           end)

    assert result.verification.owned_drops

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :cross_crate_contract &&
               guarantee.theorem == "Tail.PostUnlock.composed_contract"
           end)

    refute Enum.any?(result.verification.guarantees, &(&1.kind == :nif_adapter))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Lynx.Rust.Proofs.file!(
        result.extraction,
        options[:proof_modules]
      )

    export = Path.join(tmp, "post-unlock.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    assert File.read!(export) =~ "all_choices"
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for invalid <- [
          String.replace(source, "3#u64 13#u64 2", "3#u64 14#u64 2"),
          String.replace(source, "env.nativeRefCounter == 9", "env.nativeRefCounter == 8"),
          String.replace(
            source,
            "effects_core.increment guard.value data.counter.value",
            "effects_core.increment guard.value 0#u64"
          ),
          source <> "\nprivate axiom uncheckedPostUnlock : False\n",
          source <> "\nprivate theorem unfinishedPostUnlock : False := by sorry\n"
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
        "let changed = locked_increment(mutex, amount);\n    drop(resource);\n    changed",
        "let changed = locked_increment(mutex, amount);\n    drop(resource);\n    !changed"
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
