defmodule Lynx.Rustler.CheckedOptionTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_PURE_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR or LYNX_AENEAS_DIR")

  @tag :tmp_dir
  test "links an internal checked-arithmetic proof to the actual Option NIF implementation", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    native = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      native,
      String.replace(File.read!(native), "LynxRustFixture.Native", "LynxChecked.Native")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RustWorkspace"))

    for name <- ~w(CheckedInternal CheckedOption),
        do:
          File.cp!(
            Path.join(@fixture, "proofs/RustWorkspace/#{name}.lean"),
            Path.join(project, "RustWorkspace/#{name}.lean")
          )

    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    internal_options = [
      roots: ["experiment_analysis::analyse"],
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "internal-build"),
      module_prefix: "RustWorkspace.CheckedInternalExtraction",
      proof_modules: ["RustWorkspace.CheckedInternal"],
      required_properties:
        Enum.map(~w(core_spec caller_spec output_spec), &("RustWorkspace.CheckedInternal." <> &1))
    ]

    internal = Lynx.Rust.verify!(workspace, "experiment-analysis", internal_options)
    assert [%{status: :ok}] = internal.reports

    assert Enum.any?(internal.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract and
               row.theorem == "RustWorkspace.CheckedInternal.caller_spec" and
               Enum.any?(
                 row.implementation_dependencies,
                 &(&1["rust_name"] == "experiment_core::evaluate")
               )
           end)

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      build_dir: Path.join(tmp, "nif-build"),
      lean_project: project,
      module_prefix: "RustWorkspace.CheckedFacade",
      cargo: [features: ["checked-option"]],
      only: [checked_analyse: 1],
      proof_modules: [
        "RustWorkspace.CheckedInternalExtraction.Funs",
        "RustWorkspace.CheckedInternal",
        "RustWorkspace.CheckedOption"
      ],
      required_properties:
        Enum.map(~w(link_spec output_spec facade_spec), &("RustWorkspace.CheckedOption." <> &1))
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert Enum.any?(
             prepared.verification.external_models,
             &String.contains?(&1, "Option Try/FromResidual enum model")
           )

    assert Enum.any?(prepared.verification.guarantees, fn row ->
             row.theorem == "RustWorkspace.CheckedOption.output_spec" and
               "RustWorkspace.CheckedInternal.output_spec" in row.contracts_used
           end)

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libexperiment_nif.so"))

    stubs =
      for {name, arity, _} <- Lynx.Rustler.Metadata.inspect!(prepared.library).exports do
        "def #{name}(#{Enum.join(List.duplicate("_", arity), ", ")}), do: :erlang.nif_error(:not_loaded)"
      end

    Code.compile_string("""
    defmodule LynxChecked.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{Path.join(workspace, "priv/libexperiment_nif")}", 0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    for {value, expected} <- [
          {0, 1},
          {-1, -1},
          {4_611_686_018_427_387_903, 9_223_372_036_854_775_807},
          {-4_611_686_018_427_387_904, -9_223_372_036_854_775_807},
          {4_611_686_018_427_387_904, nil},
          {-4_611_686_018_427_387_905, nil},
          {9_223_372_036_854_775_807, nil},
          {-9_223_372_036_854_775_808, nil}
        ],
        do: assert(apply(LynxChecked.Native, :checked_analyse, [value]) == expected)

    for value <- [true, nil, 9_223_372_036_854_775_808, -9_223_372_036_854_775_809],
        do:
          assert_raise(ArgumentError, fn ->
            apply(LynxChecked.Native, :checked_analyse, [value])
          end)

    [{_, beam}] =
      Code.compile_string(~S'''
      defmodule LynxChecked.Laws do
        @compile :debug_info
        use Lynx.Laws
        law checked(value),
          requires: is_integer(value) and value >= -9223372036854775808 and value < 9223372036854775808,
          expects: LynxChecked.Native.checked_analyse(value) ==
            if(value >= -4611686018427387904 and value < 4611686018427387904, do: value * 2 + 1, else: nil),
          proof: ~LEAN"""
          cases value <;> simp [«checked:requires/1», Erlang.erlang.«is_integer/1»] at requires
          rename_i input
          have bounds : -(2^63 : Int) ≤ input ∧ input < 2^63 := by norm_num; omega
          let decoded : Aeneas.Std.I64 := Aeneas.Std.I64.ofIntCore input (by norm_num; omega)
          have decoded_val : decoded.val = input := by
            exact Aeneas.Std.I64.ofInt_val_eq _
          have decoding : Lynx.Rustler.decodeSigned .I64 64 (.integer input) = .ok decoded := by
            have encoded : Lynx.Rustler.encodeSigned decoded = .integer input := by simp [Lynx.Rustler.encodeSigned, decoded_val]
            rw [← encoded]
            exact Lynx.Rustler.decodeSigned_encodeSigned decoded
          obtain ⟨result, computed, meaning⟩ := RustWorkspace.CheckedOption.facade_spec decoded
          cases result with
          | none =>
            have outside : ¬ (-4611686018427387904 ≤ input ∧ input < 4611686018427387904) := by simpa [decoded_val] using meaning
            rcases not_and_or.mp outside with outside | outside <;>
              simp [«checked:ensures/1», Elixir.LynxChecked.Native.«checked_analyse/1»,
                Elixir.LynxChecked.Native.«checked_analyse:execution/1», decoding, computed,
                Lynx.Rustler.encodeOption, outside, Int.isLE_compare, Erlang.erlang.«==/2»]
          | some output =>
            have inside : -4611686018427387904 ≤ input ∧ input < 4611686018427387904 := by simpa [decoded_val] using And.intro meaning.1 meaning.2.1
            have output_val : output.val = input * 2 + 1 := by rw [meaning.2.2, decoded_val]; omega
            simp [«checked:ensures/1», Elixir.LynxChecked.Native.«checked_analyse/1»,
              Elixir.LynxChecked.Native.«checked_analyse:execution/1», decoding, computed,
              Lynx.Rustler.encodeOption, Lynx.Rustler.encodeSigned, output_val, inside,
              Int.isLE_compare, Erlang.erlang.«==/2»]
          """
      end
      ''')

    export = Path.join(tmp, "checked.export")
    law_options = [native: {Lynx.Rustler, options}, export: export]
    reports = Lynx.Laws.verify([beam], law_options)

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(
             for report <- reports,
                 report.status != :ok,
                 do: Map.take(report, [:module, :diagnostics])
           )

    assert Enum.all?(
             Lynx.Laws.verify([beam], Keyword.delete(law_options, :export)),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    property = Path.join(project, "RustWorkspace/CheckedOption.lean")
    original_property = File.read!(property)

    for extra <- [
          "private axiom checkedTrust : False",
          "private theorem unfinishedChecked : True := by sorry"
        ] do
      File.write!(property, original_property <> "\n" <> extra <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, original_property)
    internal_property = Path.join(project, "RustWorkspace/CheckedInternal.lean")
    original_internal = File.read!(internal_property)

    incorrect_contract =
      String.replace(
        original_internal,
        "output.val = 2 * value.val + 1",
        "output.val = 2 * value.val + 2",
        global: false
      )

    refute incorrect_contract == original_internal
    File.write!(internal_property, incorrect_contract)

    assert_raise RuntimeError, ~r/CheckedInternal.lean:/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", internal_options)
    end

    File.write!(internal_property, original_internal)

    assert [%{status: :ok}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", internal_options).reports

    core = Path.join(workspace, "core/src/lib.rs")
    original_core = File.read!(core)

    File.write!(
      core,
      String.replace(original_core, "value.checked_mul(2)", "value.checked_mul(3)")
    )

    # Preserve the previously checked internal implementation while re-extracting
    # the changed facade. The correspondence proof must reject the mismatch.
    assert_raise RuntimeError, ~r/CheckedOption.lean:/, fn -> Lynx.Rustler.prepare!(options) end

    assert_raise RuntimeError, ~r/CheckedInternal.lean:/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", internal_options)
    end

    File.write!(core, original_core)

    assert [%{status: :ok}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", internal_options).reports

    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end
end
