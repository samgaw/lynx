defmodule Lynx.Rustler.OptionTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_PURE_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR or LYNX_AENEAS_DIR for Option proofs")

  @tag :tmp_dir
  test "optional fields compose through actual Rust implementations and nested codecs", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    native = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      native,
      String.replace(File.read!(native), "LynxRustFixture.Native", "LynxOptionalFixture.Native")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RustWorkspace"))
    property = Path.join(project, "RustWorkspace/Optional.lean")
    File.cp!(Path.join(@fixture, "proofs/RustWorkspace/Optional.lean"), property)

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      build_dir: Path.join(tmp, "build"),
      lean_project: project,
      module_prefix: "RustWorkspace.OptionalFacade",
      cargo: [features: ["optional"]],
      only: [optional_flag: 1, nested_missing: 1, optional_pair: 1, optional_bytes: 1],
      proof_modules: ["RustWorkspace.Optional"],
      required_properties: [
        "RustWorkspace.Optional.core_spec",
        "RustWorkspace.Optional.caller_spec"
      ]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.count(prepared.verification.guarantees, &(&1.kind == :nif_adapter)) == 4

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract and
               evidence.theorem == "RustWorkspace.Optional.caller_spec" and
               "RustWorkspace.Optional.core_spec" in evidence.contracts_used
           end)

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libexperiment_nif.so"))

    stubs =
      for {name, arity, _flags} <- Lynx.Rustler.Metadata.inspect!(prepared.library).exports do
        arguments = Enum.map_join(1..arity, ", ", fn _ -> "_" end)
        "def #{name}(#{arguments}), do: :erlang.nif_error(:not_loaded)"
      end

    [{LynxOptionalFixture.Native, _}] =
      Code.compile_string("""
      defmodule LynxOptionalFixture.Native do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{Path.join(workspace, "priv/libexperiment_nif")}", 0)
        #{Enum.join(stubs, "\n")}
      end
      """)

    for {input, expected} <- [{nil, false}, {true, false}, {false, true}],
        do: assert(apply(LynxOptionalFixture.Native, :optional_flag, [input]) == expected)

    assert apply(LynxOptionalFixture.Native, :nested_missing, [nil]) == true
    assert apply(LynxOptionalFixture.Native, :nested_missing, [false]) == false
    assert apply(LynxOptionalFixture.Native, :optional_pair, [nil]) == nil

    assert apply(LynxOptionalFixture.Native, :optional_pair, [{true, {:ok, 256}}]) ==
             {true, {:ok, 0}}

    assert apply(LynxOptionalFixture.Native, :optional_pair, [{false, {:error, -42}}]) ==
             {false, {:error, -42}}

    assert apply(LynxOptionalFixture.Native, :optional_bytes, [nil]) == nil
    assert apply(LynxOptionalFixture.Native, :optional_bytes, [[]]) == []
    assert apply(LynxOptionalFixture.Native, :optional_bytes, [[256]]) == [0]

    assert catch_error(apply(LynxOptionalFixture.Native, :optional_bytes, [[0 | 1]])) ==
             :nif_panicked

    for {name, input} <- [
          optional_flag: 1,
          optional_flag: :other,
          optional_pair: {true, {:other, 1}},
          optional_pair: {true, {:error, 9_223_372_036_854_775_808}},
          optional_bytes: [-1 | 1]
        ] do
      assert_raise ArgumentError, fn -> apply(LynxOptionalFixture.Native, name, [input]) end
    end

    [{_, beam}] =
      Code.compile_string(~S'''
      defmodule LynxOptionalFixture.Laws do
        @compile :debug_info
        use Lynx.Laws
        law absent_flag, expects: LynxOptionalFixture.Native.optional_flag(nil) == false,
          proof: ~LEAN"""
        simp [«absent_flag:ensures/0», Elixir.LynxOptionalFixture.Native.«optional_flag/1»,
          Elixir.LynxOptionalFixture.Native.«optional_flag:execution/1»,
          experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.optional_flag,
          RustWorkspace.Optional.caller_spec, RustWorkspace.Optional.policy,
          Lynx.Rustler.decodeOption, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
          Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField, Lynx.Rustler.decodeResult,
          Lynx.Rustler.decodeUnsigned, Lynx.Rustler.decodeSigned,
          Lynx.Rustler.encodeOption, Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned,
          Lynx.Rustler.encodeSigned, Erlang.erlang.«==/2»] <;>
          norm_num [Aeneas.Std.IScalar.val, Aeneas.Std.UScalar.val, BitVec.toInt]
        """
        law present_flag, expects: LynxOptionalFixture.Native.optional_flag(false) == true,
          proof: ~LEAN"""
        simp [«present_flag:ensures/0», Elixir.LynxOptionalFixture.Native.«optional_flag/1»,
          Elixir.LynxOptionalFixture.Native.«optional_flag:execution/1»,
          experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.optional_flag,
          RustWorkspace.Optional.caller_spec, RustWorkspace.Optional.policy,
          Lynx.Rustler.decodeOption, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
          Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField, Lynx.Rustler.decodeResult,
          Lynx.Rustler.decodeUnsigned, Lynx.Rustler.decodeSigned,
          Lynx.Rustler.encodeOption, Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned,
          Lynx.Rustler.encodeSigned, Erlang.erlang.«==/2»] <;>
          norm_num [Aeneas.Std.IScalar.val, Aeneas.Std.UScalar.val, BitVec.toInt]
        """
        law nested_missing, expects: LynxOptionalFixture.Native.nested_missing(nil) == true,
          proof: ~LEAN"""
        simp [«nested_missing:ensures/0», Elixir.LynxOptionalFixture.Native.«nested_missing/1»,
          Elixir.LynxOptionalFixture.Native.«nested_missing:execution/1»,
          experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.nested_missing,
          RustWorkspace.Optional.caller_spec, RustWorkspace.Optional.policy,
          Lynx.Rustler.decodeOption, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
          Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField, Lynx.Rustler.decodeResult,
          Lynx.Rustler.decodeUnsigned, Lynx.Rustler.decodeSigned,
          Lynx.Rustler.encodeOption, Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned,
          Lynx.Rustler.encodeSigned, Erlang.erlang.«==/2»] <;>
          norm_num [Aeneas.Std.IScalar.val, Aeneas.Std.UScalar.val, BitVec.toInt]
        """
        law composite, expects: LynxOptionalFixture.Native.optional_pair({true, {:ok, 256}}) == {true, {:ok, 0}},
          proof: ~LEAN"""
        simp [«composite:ensures/0», Elixir.LynxOptionalFixture.Native.«optional_pair/1»,
          Elixir.LynxOptionalFixture.Native.«optional_pair:execution/1»,
          experiment_nif.__12.__INVENTORY.nif_func.wrapper.closure.optional_pair,
          RustWorkspace.Optional.caller_spec, RustWorkspace.Optional.policy,
          Lynx.Rustler.decodeOption, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
          Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField, Lynx.Rustler.decodeResult,
          Lynx.Rustler.decodeUnsigned, Lynx.Rustler.decodeSigned,
          Lynx.Rustler.encodeOption, Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned,
          Lynx.Rustler.encodeSigned, Erlang.erlang.«==/2»] <;>
          norm_num [Aeneas.Std.IScalar.val, Aeneas.Std.UScalar.val, BitVec.toInt]
        """
      end
      ''')

    export = Path.join(tmp, "optional.export")
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

    assert Enum.all?(
             Enum.filter(prepared.verification.guarantees, &(&1.kind == :nif_adapter)),
             fn evidence ->
               Enum.any?(evidence.codec_models, &String.contains?(&1, "Option codec"))
             end
           )

    original = File.read!(property)

    for extra <- [
          "private axiom optionalTrust : False",
          "private theorem unfinishedOption : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, String.replace(original, "| none => false", "| none => true"))
    assert_raise RuntimeError, ~r/Optional.lean:/, fn -> Lynx.Rustler.prepare!(options) end
    File.write!(property, original)
    core = Path.join(workspace, "core/src/lib.rs")
    source = File.read!(core)
    changed = String.replace(source, "None => false", "None => true")
    refute source == changed
    File.write!(core, changed)
    assert_raise RuntimeError, ~r/Optional.lean:/, fn -> Lynx.Rustler.prepare!(options) end
    File.write!(core, source)
    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end
end
