defmodule Lynx.Rustler.ScalarVecTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_PURE_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR or LYNX_AENEAS_DIR for scalar-list proofs")

  @tag :tmp_dir
  test "scalar lists retain element semantics through a cross-crate update", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxRustFixture.Native", "LynxScalarFixture.Native")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RustWorkspace"))
    property = Path.join(project, "RustWorkspace/ScalarVec.lean")
    File.cp!(Path.join(@fixture, "proofs/RustWorkspace/ScalarVec.lean"), property)

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      build_dir: Path.join(tmp, "build"),
      lean_project: project,
      module_prefix: "RustWorkspace.ScalarFacade",
      cargo: [features: ["scalar-vec"]],
      only: [replace_first_i64: 2, echo_flags: 1, echo_signed_bytes: 1],
      proof_modules: ["RustWorkspace.ScalarVec"],
      required_properties:
        Enum.map(
          ~w(slice_transition vector_transition composition preserves_length),
          &("RustWorkspace.ScalarVec." <> &1)
        )
    ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.count(prepared.verification.guarantees, &(&1.kind == :nif_adapter)) == 3

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract and
               evidence.theorem == "RustWorkspace.ScalarVec.composition" and
               "RustWorkspace.ScalarVec.vector_transition" in evidence.contracts_used
           end)

    assert Enum.any?(
             prepared.verification.external_models,
             &String.contains?(&1, "scalar Vec codec")
           )

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libexperiment_nif.so"))

    stubs =
      for {name, arity, _} <- Lynx.Rustler.Metadata.inspect!(prepared.library).exports do
        arguments = Enum.map_join(1..arity, ", ", fn _ -> "_" end)
        "def #{name}(#{arguments}), do: :erlang.nif_error(:not_loaded)"
      end

    Code.compile_string("""
    defmodule LynxScalarFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{Path.join(workspace, "priv/libexperiment_nif")}", 0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert apply(LynxScalarFixture.Native, :replace_first_i64, [[-1, 42], 7]) == {true, [7, 42]}
    assert apply(LynxScalarFixture.Native, :replace_first_i64, [[], 7]) == {false, []}
    assert apply(LynxScalarFixture.Native, :echo_flags, [[true, false]]) == [true, false]
    assert apply(LynxScalarFixture.Native, :echo_signed_bytes, [[128]]) == [-128]

    assert catch_error(apply(LynxScalarFixture.Native, :echo_flags, [[true | 7]])) ==
             :nif_panicked

    for {name, arguments} <- [
          replace_first_i64: [[9_223_372_036_854_775_808], 7],
          replace_first_i64: [[-9_223_372_036_854_775_809], 7],
          echo_flags: [[1 | 7]],
          echo_flags: [nil],
          echo_signed_bytes: [[2_147_483_648]]
        ] do
      assert_raise ArgumentError, fn -> apply(LynxScalarFixture.Native, name, arguments) end
    end

    [{_, beam}] =
      Code.compile_string(~S'''
      defmodule LynxScalarFixture.Laws do
        @compile :debug_info
        use Lynx.Laws
        law updates_field, expects: LynxScalarFixture.Native.replace_first_i64([-1, 42], 7) == {true, [7, 42]},
          proof: ~LEAN"""
          simp [«updates_field:ensures/0», Elixir.LynxScalarFixture.Native.«replace_first_i64/2»,
            Elixir.LynxScalarFixture.Native.«replace_first_i64:execution/2»,
            RustWorkspace.ScalarVec.facade_spec,
            Lynx.Rustler.decodeSigned, Lynx.Rustler.encodeBool,
            Lynx.Rustler.encodeScalarVec, Lynx.Rustler.byteVecLimit, Lynx.Rustler.encodeSigned,
            Aeneas.Std.alloc.vec.Vec.val,
            Aeneas.Std.Slice.set_val_eq, Erlang.erlang.«==/2»] <;>
            norm_num [Aeneas.Std.IScalar.val, BitVec.toInt]
          rw [RustWorkspace.ScalarVec.input_decoded]
          simp [RustWorkspace.ScalarVec.inputVector, Aeneas.Std.alloc.vec.Vec.val,
            Aeneas.Std.alloc.vec.Vec.from, Lynx.Rustler.encodeScalarVec,
            Lynx.Rustler.byteVecLimit, Lynx.Rustler.encodeSigned, Lynx.Rustler.encodeBool,
            Aeneas.Std.Slice.set_val_eq] <;>
            norm_num [Aeneas.Std.IScalar.val, BitVec.toInt]
          """
        law flags_roundtrip, expects: LynxScalarFixture.Native.echo_flags([true, false]) == [true, false],
          proof: ~LEAN"""
          simp [«flags_roundtrip:ensures/0», Elixir.LynxScalarFixture.Native.«echo_flags/1»,
            Elixir.LynxScalarFixture.Native.«echo_flags:execution/1»,
            experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.echo_flags,
            Aeneas.Std.alloc.vec.Vec.val,
            Lynx.Rustler.encodeScalarVec, Lynx.Rustler.byteVecLimit, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
          rw [RustWorkspace.ScalarVec.flags_decoded]
          simp [RustWorkspace.ScalarVec.flagsVector, Aeneas.Std.alloc.vec.Vec.val,
            Aeneas.Std.alloc.vec.Vec.from, Lynx.Rustler.encodeScalarVec,
            Lynx.Rustler.byteVecLimit, Lynx.Rustler.encodeSigned, Lynx.Rustler.encodeBool,
            Aeneas.Std.Slice.set_val_eq] <;>
            norm_num [Aeneas.Std.IScalar.val, BitVec.toInt]
          """
        law signed_narrowing, expects: LynxScalarFixture.Native.echo_signed_bytes([128]) == [-128],
          proof: ~LEAN"""
          simp [«signed_narrowing:ensures/0», Elixir.LynxScalarFixture.Native.«echo_signed_bytes/1»,
            Elixir.LynxScalarFixture.Native.«echo_signed_bytes:execution/1»,
            experiment_nif.__12.__INVENTORY.nif_func.wrapper.closure.echo_signed_bytes,
            Aeneas.Std.alloc.vec.Vec.val, Aeneas.Std.alloc.vec.Vec.from,
            Lynx.Rustler.encodeScalarVec, Lynx.Rustler.byteVecLimit, Lynx.Rustler.encodeSigned, Erlang.erlang.«==/2»] <;>
            norm_num [Aeneas.Std.IScalar.val, BitVec.toInt]
          rw [RustWorkspace.ScalarVec.signed_decoded]
          simp [RustWorkspace.ScalarVec.signedVector, Aeneas.Std.alloc.vec.Vec.val,
            Aeneas.Std.alloc.vec.Vec.from, Lynx.Rustler.encodeScalarVec,
            Lynx.Rustler.byteVecLimit, Lynx.Rustler.encodeSigned, Lynx.Rustler.encodeBool,
            Aeneas.Std.Slice.set_val_eq] <;>
            norm_num [Aeneas.Std.IScalar.val, BitVec.toInt]
          """
      end
      ''')

    export = Path.join(tmp, "scalar.export")
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

    original = File.read!(property)

    for extra <- [
          "private axiom scalarTrust : False",
          "private theorem unfinishedScalar : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(
      property,
      String.replace(original, "input.slice.set 0#usize", "input.slice.set 1#usize")
    )

    assert_raise RuntimeError, ~r/ScalarVec.lean:/, fn -> Lynx.Rustler.prepare!(options) end
    File.write!(property, original)
    core = Path.join(workspace, "core/src/collections.rs")
    original_core = File.read!(core)

    [prefix, implementation] =
      String.split(original_core, "pub fn replace_slice_first_i64", parts: 2)

    changed =
      prefix <>
        "pub fn replace_slice_first_i64" <>
        String.replace(implementation, "input[0] = value", "input[0] = 0", global: false)

    refute changed == original_core
    File.write!(core, changed)
    assert_raise RuntimeError, ~r/ScalarVec.lean:/, fn -> Lynx.Rustler.prepare!(options) end
    File.write!(core, original_core)
    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end
end
