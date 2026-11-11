defmodule Lynx.Rustler.DerivedMapDecoderTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_PURE_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR for derived Decoder proofs")

  @tag :tmp_dir
  test "verifies actual map decoding, error cleanup and composed native calls", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    native = Path.join(workspace, "nif/src/lib.rs")

    original =
      File.read!(native) |> String.replace("LynxRustFixture.Native", "LynxDerivedDecode.Native")

    File.write!(native, original)
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RustWorkspace"))
    property = Path.join(project, "RustWorkspace/DerivedMapDecoder.lean")
    proof = File.read!(Path.join(@fixture, "proofs/RustWorkspace/DerivedMapDecoder.lean"))
    File.write!(property, proof)
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      build_dir: Path.join(tmp, "build"),
      lean_project: project,
      module_prefix: "RustWorkspace.MapDecodeFacade",
      cargo: [features: ["derived-map-decoder"]],
      only: [ordered_map: 1],
      proof_modules: ["RustWorkspace.DerivedMapDecoder"],
      required_properties:
        Enum.map(
          ~w(core_spec caller_spec field_success decoder_success field_low_error facade_spec encoder_spec),
          &("RustWorkspace.DerivedMapDecoder." <> &1)
        )
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert Enum.any?(
             prepared.verification.guarantees,
             &(&1.kind == :nif_adapter and &1.status == :verified)
           )

    assert Enum.count(prepared.verification.guarantees, &(&1.kind == :rust_implementation)) >= 5

    assert Enum.any?(
             prepared.verification.external_models,
             &String.contains?(&1, "boxed errors exhaust verification")
           )

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libexperiment_nif.so"))

    stubs =
      for {name, arity, _} <- Lynx.Rustler.Metadata.inspect!(prepared.library).exports do
        args = Enum.join(List.duplicate("_", arity), ", ")
        "def #{name}(#{args}), do: :erlang.nif_error(:not_loaded)"
      end

    [{native_module, _}] =
      Code.compile_string("""
      defmodule LynxDerivedDecode.Native do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{Path.join(workspace, "priv/libexperiment_nif")}", 0)
        #{Enum.join(stubs, "\n")}
      end
      """)

    assert apply(native_module, :ordered_map, [%{low: 9, high: 4, extra: true}]) == %{
             low: 4,
             high: 9
           }

    for input <- [%{}, %{low: 4}, :not_a_map] do
      assert_raise ArgumentError, fn -> apply(native_module, :ordered_map, [input]) end
    end

    for bad <- [-1, 18_446_744_073_709_551_616, true, "1"] do
      assert catch_error(apply(native_module, :ordered_map, [%{low: bad, high: 4}])) ==
               "Could not decode field :low on %{}"

      assert catch_error(apply(native_module, :ordered_map, [%{low: 4, high: bad}])) ==
               "Could not decode field :high on %{}"
    end

    [{_, beam}] =
      Code.compile_string(~S'''
      defmodule LynxDerivedDecode.Laws do
        @compile :debug_info
        use Lynx.Laws
        law orders_decoded_fields(left, right),
          requires: is_integer(left) and is_integer(right) and left >= 0 and right >= 0 and
            left <= 18_446_744_073_709_551_615 and right <= 18_446_744_073_709_551_615,
          expects: :erlang.map_get(:low, LynxDerivedDecode.Native.ordered_map(%{low: left, high: right})) == if(left <= right, do: left, else: right),
          proof: ~LEAN"""
          cases left <;> cases right <;>
            simp [«orders_decoded_fields:requires/2», Erlang.erlang.«is_integer/1»] at requires
          rename_i a b
          have arange : 0 ≤ a ∧ a < (2^64 : Int) := by norm_num; omega
          have brange : 0 ≤ b ∧ b < (2^64 : Int) := by norm_num; omega
          let l : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore a.toNat (by norm_num; omega)
          let r : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore b.toNat (by norm_num; omega)
          have lv : (l.val : Int) = a := by simp only [l, Aeneas.Std.U64.ofNatCore, Aeneas.Std.UScalar.ofNatCore_val_eq, Int.toNat_of_nonneg arange.1]
          have rv : (r.val : Int) = b := by simp only [r, Aeneas.Std.U64.ofNatCore, Aeneas.Std.UScalar.ofNatCore_val_eq, Int.toNat_of_nonneg brange.1]
          have foundLow : Lynx.Term.mapLookup [(.atom "high", .integer b), (.atom "low", .integer a)] (.atom "low") = some (Lynx.Rustler.encodeUnsigned l) := by simp [Lynx.Term.mapLookup, Lynx.Rustler.encodeUnsigned, lv]
          have foundHigh : Lynx.Term.mapLookup [(.atom "high", .integer b), (.atom "low", .integer a)] (.atom "high") = some (Lynx.Rustler.encodeUnsigned r) := by simp [Lynx.Term.mapLookup, Lynx.Rustler.encodeUnsigned, rv]
          have decoded := RustWorkspace.DerivedMapDecoder.decoder_success _ l r foundLow foundHigh
          by_cases ordered : a ≤ b
          · have rust_ordered : l ≤ r := by change l.val ≤ r.val; omega
            simp [«orders_decoded_fields:ensures/2», Elixir.LynxDerivedDecode.Native.«ordered_map/1»,
              Elixir.LynxDerivedDecode.Native.«ordered_map:execution/1», decoded, rust_ordered,
              RustWorkspace.DerivedMapDecoder.facade_spec, RustWorkspace.DerivedMapDecoder.encoder_spec,
              Lynx.Rustler.Decoding.withDecoded, Lynx.Rustler.execute, lv, rv, ordered, Int.isLE_compare,
              Erlang.erlang.«map_get/2», Lynx.Term.mapLookup, Erlang.erlang.«==/2»]
          · have rust_ordered : ¬ l ≤ r := by change ¬ l.val ≤ r.val; omega
            simp [«orders_decoded_fields:ensures/2», Elixir.LynxDerivedDecode.Native.«ordered_map/1»,
              Elixir.LynxDerivedDecode.Native.«ordered_map:execution/1», decoded, rust_ordered,
              RustWorkspace.DerivedMapDecoder.facade_spec, RustWorkspace.DerivedMapDecoder.encoder_spec,
              Lynx.Rustler.Decoding.withDecoded, Lynx.Rustler.execute, lv, rv, ordered, Int.isLE_compare,
              Erlang.erlang.«map_get/2», Lynx.Term.mapLookup, Erlang.erlang.«==/2»]
          """
      end
      ''')

    export = Path.join(tmp, "derived-decoder.export")
    law_options = [native: {Lynx.Rustler, options}, export: export]
    reports = Lynx.Laws.verify([beam], law_options)

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(for r <- reports, r.status != :ok, do: Map.take(r, [:module, :diagnostics]))

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    assert Enum.all?(
             Lynx.Laws.verify([beam], Keyword.delete(law_options, :export)),
             &(&1.status == :ok and &1.cached)
           )

    for unfinished <- [
          "private axiom unjustifiedDecode : False",
          "private theorem unfinishedDecode : True := by sorry"
        ] do
      File.write!(property, proof <> "\n" <> unfinished <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, proof)
    core = Path.join(workspace, "core/src/lib.rs")
    original_core = File.read!(core)
    File.write!(core, String.replace(original_core, "if left <= right", "if left >= right"))
    assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    File.write!(core, original_core)
    assert Lynx.Rustler.prepare!(options).verification.guarantees != []
  end
end
