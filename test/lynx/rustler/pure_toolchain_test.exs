defmodule Lynx.Rustler.PureToolchainTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_PURE_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "profile=pure"),
         do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR to an installation made with --pure")

  @tag :tmp_dir
  test "proves compiled workspace NIFs with unmodified Aeneas and rejects unsupported semantics",
       %{
         tmp_dir: tmp
       } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    native = Path.join(workspace, "nif/src/lib.rs")
    native_source = File.read!(native) |> String.replace("LynxRustFixture", "LynxPureFixture")
    File.write!(native, native_source)

    for name <- ~w(native.ex laws.ex) do
      path = Path.join(workspace, "elixir/" <> name)
      File.write!(path, File.read!(path) |> String.replace("LynxRustFixture", "LynxPureFixture"))
    end

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RustWorkspace"))

    for name <- ~w(Native BridgeTests),
        do:
          File.cp!(
            Path.join(@fixture, "proofs/RustWorkspace/" <> name <> ".lean"),
            Path.join(project, "RustWorkspace/" <> name <> ".lean")
          )

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      build_dir: Path.join(tmp, "build"),
      lean_project: project,
      module_prefix: "RustWorkspace.Facade",
      proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"],
      required_properties:
        Enum.map(
          ~w(invert_spec analysis_spec facade_spec double_spec integer_composition integer_facade),
          &("RustWorkspace.Native." <> &1)
        ) ++ ["RustWorkspace.BridgeTests.overflow_is_panic"]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert %{"aeneas_version" => "build-2b9e3ea", "charon_version" => "0.1.304"} =
             prepared.extraction.translation

    refute Map.has_key?(prepared.extraction.translation, "effectful_calls_preserved")
    assert Enum.count(prepared.verification.guarantees, &(&1.kind == :nif_adapter)) == 10

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract &&
               evidence.theorem == "RustWorkspace.Native.integer_composition" &&
               "RustWorkspace.Native.double_spec" in evidence.contracts_used
           end)

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libexperiment_nif.so"))
    Code.compile_file(Path.join(workspace, "elixir/native.ex"))
    assert apply(LynxPureFixture.Native, :restore, [true]) == true
    assert apply(LynxPureFixture.Native, :restore, [false]) == false
    assert apply(LynxPureFixture.Native, :calculate, [21]) == 43
    assert apply(LynxPureFixture.Native, :echo_i8, [128]) == -128

    assert catch_error(apply(LynxPureFixture.Native, :calculate, [4_611_686_018_427_387_904])) ==
             :nif_panicked

    assert_raise ArgumentError, fn ->
      apply(LynxPureFixture.Native, :calculate, [9_223_372_036_854_775_808])
    end

    [{LynxPureFixture.Laws, beam}] = Code.compile_file(Path.join(workspace, "elixir/laws.ex"))
    export = Path.join(tmp, "pure-native.export")
    law_options = [native: {Lynx.Rustler, options}, export: export]
    assert_verified(Lynx.Laws.verify([beam], law_options))

    assert Enum.all?(
             Lynx.Laws.verify([beam], Keyword.delete(law_options, :export)),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    unrelated = Path.join(workspace, "unrelated/src/lib.rs")
    unrelated_source = File.read!(unrelated)

    changed_unrelated =
      String.replace(unrelated_source, "\n    value\n", "\n    value.wrapping_add(1)\n")

    refute changed_unrelated == unrelated_source
    File.write!(unrelated, changed_unrelated)
    repeated = Lynx.Rustler.prepare!(options)
    assert repeated.extraction.fingerprint == prepared.extraction.fingerprint
    assert Enum.all?(repeated.reports, &(&1.status == :ok and &1.cached))

    property = Path.join(project, "RustWorkspace/Native.lean")
    original = File.read!(property)

    for extra <- [
          "private axiom pureTrust : False",
          "private theorem unfinishedPure : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert error.message =~ "audit"
    end

    wrong =
      String.replace(original, "result.val = value.val * 2 + 1", "result.val = value.val * 2 + 2")

    refute wrong == original
    File.write!(property, wrong)
    error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    assert error.message =~ "Native.lean:"
    File.write!(property, original)

    core = Path.join(workspace, "core/src/lib.rs")
    core_source = File.read!(core)
    changed = String.replace(core_source, "value * 2", "value * 3")
    refute changed == core_source
    File.write!(core, changed)
    error = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    assert error.message =~ "Native.lean:"
    File.write!(core, core_source)

    # Stock Aeneas must never erase an observable destructor and verify the old law.
    observable = """
    struct Flip<'a>(&'a mut bool);
    impl Drop for Flip<'_> { fn drop(&mut self) { *self.0 = !*self.0; } }
    let mut observed = value;
    { let _guard = Flip(&mut observed); }
    observed
    """

    changed =
      String.replace(native_source, "experiment_analysis::restore(value)", observable,
        global: false
      )

    refute changed == native_source
    File.write!(native, changed)
    assert_raise CompileError, ~r/drop|destructor/i, fn -> Lynx.Rustler.prepare!(options) end

    changed =
      String.replace(
        native_source,
        "experiment_analysis::twice_plus_one(value)",
        "let _message = value.to_string(); experiment_analysis::twice_plus_one(value)"
      )

    refute changed == native_source
    File.write!(native, changed)

    assert_raise ArgumentError, ~r/bounded formatting library/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(native, native_source)
    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end

  defp assert_verified(reports) do
    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(
             for report <- reports,
                 report.status != :ok,
                 do: Map.take(report, [:module, :diagnostics])
           )
  end
end
