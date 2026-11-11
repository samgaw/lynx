defmodule Lynx.Rustler.DerivedTupleDecoderTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_JOIN_RECOVERY_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_JOIN_RECOVERY_AENEAS_DIR for derived tuple Decoder proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "verifies actual tuple decoding and composed native calls with Rustler #{version}", %{
      tmp_dir: tmp
    } do
      version = unquote(version)
      prefix = "LynxDerivedTupleDecode" <> String.replace(version, ".", "")
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

      native = Path.join(workspace, "nif/src/lib.rs")

      original =
        File.read!(native)
        |> String.replace("LynxRustFixture.Native", prefix <> ".Native")

      File.write!(native, original)
      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "RustWorkspace"))
      property = Path.join(project, "RustWorkspace/DerivedTupleDecoder.lean")
      proof = File.read!(Path.join(@fixture, "proofs/RustWorkspace/DerivedTupleDecoder.lean"))
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
        module_prefix: "RustWorkspace.TupleDecodeFacade",
        cargo: [features: ["derived-tuple-decoder"]],
        only: [ordered_tuple: 1],
        proof_modules: ["RustWorkspace.DerivedTupleDecoder"],
        required_properties:
          Enum.map(
            ~w(core_spec caller_spec ordered_fields field_success decoder_success non_tuple arity_rejected oversized field_low_error field_high_error decoder_low_error decoder_high_error facade_spec encoder_spec),
            &("RustWorkspace.DerivedTupleDecoder." <> &1)
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
        defmodule #{prefix}.Native do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(~c"#{Path.join(workspace, "priv/libexperiment_nif")}", 0)
          #{Enum.join(stubs, "\n")}
        end
        """)

      assert apply(native_module, :ordered_tuple, [{9, 4}]) == {4, 9}

      for input <- [:not_a_tuple, [], %{}, {}, {4}, {4, 9, 12}] do
        assert_raise ArgumentError, fn -> apply(native_module, :ordered_tuple, [input]) end
      end

      for bad <- [-1, 18_446_744_073_709_551_616, true, "1"] do
        assert catch_error(apply(native_module, :ordered_tuple, [{bad, 4}])) ==
                 "Could not decode field low on OrderedFields"

        assert catch_error(apply(native_module, :ordered_tuple, [{4, bad}])) ==
                 "Could not decode field high on OrderedFields"
      end

      [{_, beam}] =
        Code.compile_string(
          ~S'''
          defmodule LynxDerivedTupleDecode.Laws do
            @compile :debug_info
            use Lynx.Laws
            law orders_decoded_fields(left, right),
              requires: is_integer(left) and is_integer(right) and left >= 0 and right >= 0 and
                left <= 18_446_744_073_709_551_615 and right <= 18_446_744_073_709_551_615,
              expects: :erlang.element(1, LynxDerivedTupleDecode.Native.ordered_tuple({left, right})) == if(left <= right, do: left, else: right),
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
              have decoded : experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode
                  (.tuple #[.integer a, .integer b]) = Aeneas.Std.RustM.ok (.Ok {low := l, high := r}) := by
                simpa only [Lynx.Rustler.encodeUnsigned, lv, rv] using
                  RustWorkspace.DerivedTupleDecoder.decoder_success l r
              by_cases ordered : a ≤ b
              · have rust_ordered : l ≤ r := by change l.val ≤ r.val; omega
                simp [«orders_decoded_fields:ensures/2», Elixir.LynxDerivedTupleDecode.Native.«ordered_tuple/1»,
                  Elixir.LynxDerivedTupleDecode.Native.«ordered_tuple:execution/1», decoded, rust_ordered,
                  RustWorkspace.DerivedTupleDecoder.facade_spec, RustWorkspace.DerivedTupleDecoder.encoder_spec,
                  Lynx.Rustler.Decoding.withDecoded, Lynx.Rustler.execute, lv, rv, ordered, Int.isLE_compare,
                  Erlang.erlang.«element/2», Erlang.erlang.«==/2»]
              · have rust_ordered : ¬ l ≤ r := by change ¬ l.val ≤ r.val; omega
                simp [«orders_decoded_fields:ensures/2», Elixir.LynxDerivedTupleDecode.Native.«ordered_tuple/1»,
                  Elixir.LynxDerivedTupleDecode.Native.«ordered_tuple:execution/1», decoded, rust_ordered,
                  RustWorkspace.DerivedTupleDecoder.facade_spec, RustWorkspace.DerivedTupleDecoder.encoder_spec,
                  Lynx.Rustler.Decoding.withDecoded, Lynx.Rustler.execute, lv, rv, ordered, Int.isLE_compare,
                  Erlang.erlang.«element/2», Erlang.erlang.«==/2»]
              """
          end
          '''
          |> String.replace("LynxDerivedTupleDecode", prefix)
        )

      export = Path.join(tmp, "derived-decoder.export")
      law_options = [native: {Lynx.Rustler, options}, export: export]
      reports = Lynx.Laws.verify([beam], law_options)

      assert Enum.all?(reports, &(&1.status == :ok)),
             inspect(for r <- reports, r.status != :ok, do: Map.take(r, [:module, :diagnostics]))

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

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

      File.write!(
        property,
        proof <>
          """
          theorem incorrect_arity_contract (first second third : Lynx.Term) :
              experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode (.tuple #[first, second, third]) =
                Aeneas.Std.RustM.ok (.Ok {low := 0#u64, high := 0#u64}) := by
            have bounds : (3 : Nat) ≤ Aeneas.Std.Usize.max ∧ 3 ≤ Aeneas.Std.Isize.max.toNat ∧ 3 ≤ 16777215 := by scalar_tac
            have rejected := RustWorkspace.DerivedTupleDecoder.arity_rejected #[first, second, third]
              (by simpa using bounds) (by simp)
            rw [rejected]
          """
      )

      failure = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert Exception.message(failure) =~ "DerivedTupleDecoder.lean"
      File.write!(property, proof)
      core = Path.join(workspace, "core/src/lib.rs")
      original_core = File.read!(core)
      File.write!(core, String.replace(original_core, "if left <= right", "if left >= right"))
      failure = assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      assert Exception.message(failure) =~ "DerivedTupleDecoder.lean"
      File.write!(core, original_core)
      assert Lynx.Rustler.prepare!(options).verification.guarantees != []
    end
  end
end
