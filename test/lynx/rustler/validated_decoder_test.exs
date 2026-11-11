defmodule Lynx.Rustler.ValidatedDecoderTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do:
      @moduletag(
        skip: "set LYNX_UNPATCHED_AENEAS_DIR or LYNX_AENEAS_DIR for validated Decoder proofs"
      )

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "proves actual Rustler BadArg validation with Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = String.replace(version, ".", "")
      native_module = "LynxValidated#{suffix}.Native"
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for name <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
          do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))
      native = Path.join(workspace, "nif/src/lib.rs")
      source = String.replace(File.read!(native), "LynxRustFixture.Native", native_module)

      source =
        if @unpatched do
          "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
            Enum.reduce(~w(validated_result validated_flag), source, fn name, source ->
              String.replace(source, "fn #{name}(", "#[verify::start_from]\nfn #{name}(")
            end)
        else
          source
        end

      File.write!(native, source)

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "Validated"))
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        root_attribute: if(@unpatched, do: "verify::start_from"),
        cargo: [features: ["validated-decoder"]],
        only: [validated_result: 1, validated_flag: 1],
        mir: nil,
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "Validated.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)
      by_name = Map.new(prepared.bindings.bindings, &{&1["name"], &1})
      [argument] = by_name["validated_flag"]["arguments"]
      assert %{"decoder" => decoder} = argument

      assert %{sites: [_, _], variant: %{"name" => "BadArg", "fields" => []}} =
               prepared.extraction.rustler_constructors

      properties =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/Validated.lean"))
        |> String.replace("__DECODER__", decoder)
        |> String.replace("__FLAG__", by_name["validated_flag"]["lean_name"])
        |> String.replace("__RESULT__", by_name["validated_result"]["lean_name"])

      property = Path.join(project, "Validated/Properties.lean")
      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["Validated.Properties"],
            required_properties:
              Enum.map(
                ~w(invert_spec restore_spec validation_spec validation_error decoder_spec flag_spec result_spec zero_rejected),
                &("Validated.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :rust_implementation and
                   &1.theorem == "Validated.Properties.validation_spec")
             )

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :cross_crate_contract and
                   &1.theorem == "Validated.Properties.restore_spec")
             )

      assert Enum.any?(prepared.verification.unverified_external_calls, fn model ->
               model.rust_name == "rustler::error::Error::BadArg" and
                 model.implementation_verified == false
             end)

      assert Enum.any?(
               prepared.verification.trusted_boundary,
               &String.contains?(&1, "validated lowering")
             )

      library = Path.join(tmp, "validated_native")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {name, arity, _} <- prepared.bindings.exports do
          "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"
        end

      [{native_atom, _}] =
        Code.compile_string("""
        defmodule #{native_module} do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
          #{Enum.join(stubs, "\n")}
        end
        """)

      for name <- [:validated_flag, :validated_result] do
        for value <- [1, 7, 18_446_744_073_709_551_615],
            do: assert(apply(native_atom, name, [value]) == true)

        for value <- [0, -1, 18_446_744_073_709_551_616, :invalid],
            do: assert_raise(ArgumentError, fn -> apply(native_atom, name, [value]) end)
      end

      [{_, beam}] = Code.compile_string(laws(native_module, suffix))
      export = Path.join(tmp, "validated.export")
      reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
      stable = Lynx.Rustler.prepare!(options)
      stable_options = [lean_project: project, externals: [stable.external]]
      assert Enum.all?(Lynx.Laws.verify([beam], stable_options), &(&1.status == :ok))

      assert Enum.all?(
               Lynx.Laws.verify([beam], stable_options),
               &(&1.status == :ok and &1.cached)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      for extra <- [
            "private axiom constructorTrust : False",
            "private theorem unfinishedConstructor : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      wrong = String.replace(properties, ".atom \"badarg\"", ".atom \"wrong\"")
      refute wrong == properties
      File.write!(property, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(property, properties)
      changed = String.replace(source, "if value == 0", "if value != 0")
      refute changed == source
      File.write!(native, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      # Every error from this validator is BadArg. Discarding and rebuilding
      # that error is supported, with scalar Ok cleanup retained explicitly.
      discarded =
        String.replace(
          source,
          "Err(error) => Err(error)",
          "Err(_) => Err(rustler::Error::BadArg)"
        )

      File.write!(native, discarded)

      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

      assert Enum.all?(
               Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
               &(&1.status == :ok)
             )

      # A separate internal root has no Error constructors or NIF exposure.
      # Its scalar Result cleanup completes for BadArg, but must not assume
      # that an arbitrary boxed error has an unobservable destructor.
      File.write!(
        native,
        source <>
          """

          pub fn discard_error(error: rustler::Error) -> bool {
              let _result: Result<bool, _> = Err(error);
              true
          }

          pub fn discard_result(result: Result<bool, rustler::Error>) -> bool {
              let _result = result;
              true
          }

          pub fn discard_direct(error: rustler::Error) -> bool {
              let _error = error;
              true
          }

          pub fn result_to_option(value: Result<bool, rustler::Error>) -> Option<bool> {
              value.ok()
          }

          pub fn option_to_result(value: Option<bool>, error: rustler::Error) -> Result<bool, rustler::Error> {
              value.ok_or(error)
          }
          """
      )

      File.mkdir_p!(Path.join(project, "Validated"))
      scalar_property = Path.join(project, "Validated/ScalarProperties.lean")

      scalar_proof = """
      module
      public import Validated.Scalar.Funs
      public section
      open Aeneas Aeneas.Std
      namespace Validated.ScalarProperties
      theorem static_error : experiment_nif.discard_error Lynx.Rustler.badArgOutcome = RustM.ok true := by
        simp [experiment_nif.discard_error, Lynx.Rustler.Decoding.dropScalarResult,
          Lynx.Rustler.Decoding.dropDecoderError, Lynx.Rustler.badArgOutcome]
      theorem direct_static_error : experiment_nif.discard_direct Lynx.Rustler.badArgOutcome = RustM.ok true := by
        simp [experiment_nif.discard_direct, Lynx.Rustler.Decoding.dropDecoderError,
          Lynx.Rustler.badArgOutcome]
      theorem scalar_success (value : Bool) :
          experiment_nif.discard_result (.Ok value) = RustM.ok true := by
        simp [experiment_nif.discard_result, Lynx.Rustler.Decoding.dropScalarResult]
      theorem result_some (value : Bool) : experiment_nif.result_to_option (.Ok value) = RustM.ok (some value) := by
        simp [experiment_nif.result_to_option, Lynx.Rustler.Decoding.resultOk]
      theorem result_none : experiment_nif.result_to_option (.Err Lynx.Rustler.badArgOutcome) = RustM.ok none := by
        simp [experiment_nif.result_to_option, Lynx.Rustler.Decoding.resultOk,
          Lynx.Rustler.Decoding.dropDecoderError, Lynx.Rustler.badArgOutcome]
      theorem result_boxed (raises : Bool) (encode : Lynx.Rustler.Env → RustM Lynx.Rustler.NativeTerm) :
          experiment_nif.result_to_option (.Err (.encoded raises encode)) = RustM.fail .undef := by
        simp [experiment_nif.result_to_option, Lynx.Rustler.Decoding.resultOk,
          Lynx.Rustler.Decoding.dropDecoderError]
      theorem option_none (error : Lynx.Rustler.DecoderError) :
          experiment_nif.option_to_result none error = RustM.ok (.Err error) := by
        simp [experiment_nif.option_to_result, Lynx.Rustler.Decoding.optionOkOr]
      theorem option_some (value : Bool) :
          experiment_nif.option_to_result (some value) Lynx.Rustler.badArgOutcome = RustM.ok (.Ok value) := by
        simp [experiment_nif.option_to_result, Lynx.Rustler.Decoding.optionOkOr,
          Lynx.Rustler.Decoding.dropDecoderError, Lynx.Rustler.badArgOutcome]
      theorem option_boxed (value raises : Bool) (encode : Lynx.Rustler.Env → RustM Lynx.Rustler.NativeTerm) :
          experiment_nif.option_to_result (some value) (.encoded raises encode) = RustM.fail .undef := by
        simp [experiment_nif.option_to_result, Lynx.Rustler.Decoding.optionOkOr,
          Lynx.Rustler.Decoding.dropDecoderError]
      end Validated.ScalarProperties
      """

      File.write!(scalar_property, scalar_proof)

      scalar_options = [
        tools: @tools,
        roots: [
          "experiment_nif::discard_error",
          "experiment_nif::discard_result",
          "experiment_nif::discard_direct",
          "experiment_nif::result_to_option",
          "experiment_nif::option_to_result"
        ],
        cargo: [features: ["validated-decoder"]],
        lean_project: project,
        build_dir: Path.join(tmp, "scalar-build"),
        module_prefix: "Validated.Scalar",
        external_types: [
          %{
            rust: "rustler::error::Error",
            lean: "Lynx.Rustler.DecoderError",
            import: "Validated.RustlerBridge",
            label: "Rustler error outcome model; native SDK/FFI unverified"
          }
        ],
        mir: :elaborated,
        external_calls: [:rustler_decoders],
        proof_modules: ["Validated.ScalarProperties"],
        required_properties: [
          "Validated.ScalarProperties.static_error",
          "Validated.ScalarProperties.scalar_success",
          "Validated.ScalarProperties.direct_static_error",
          "Validated.ScalarProperties.result_some",
          "Validated.ScalarProperties.result_none",
          "Validated.ScalarProperties.result_boxed",
          "Validated.ScalarProperties.option_none",
          "Validated.ScalarProperties.option_some",
          "Validated.ScalarProperties.option_boxed"
        ]
      ]

      scalar = Lynx.Rust.verify!(workspace, "experiment-nif", scalar_options)

      assert Enum.any?(
               scalar.verification.guarantees,
               &(&1.theorem == "Validated.ScalarProperties.static_error")
             )

      File.write!(
        scalar_property,
        scalar_proof <>
          """
          theorem unproved_boxed_drop :
              experiment_nif.discard_error (.encoded false (fun _ => RustM.ok .nil)) = RustM.ok true := by
            simp [experiment_nif.discard_error, Lynx.Rustler.Decoding.dropScalarResult,
              Lynx.Rustler.Decoding.dropDecoderError]
          """
      )

      failure =
        assert_raise RuntimeError, fn ->
          Lynx.Rust.verify!(workspace, "experiment-nif", scalar_options)
        end

      assert Exception.message(failure) =~ "Validated/ScalarProperties.lean"
      File.write!(scalar_property, scalar_proof)

      File.write!(native, source)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end

  defp laws(native, suffix) do
    laws =
      for target <- ~w(validated_flag validated_result), into: "" do
        """
        law #{target}_positive(value),
          requires: is_integer(value) and value > 0 and value <= 18_446_744_073_709_551_615,
          expects: #{native}.#{target}(value) == true,
          proof: ~LEAN\"\"\"
          cases value <;> simp [«#{target}_positive:requires/1», Erlang.erlang.«is_integer/1»] at requires
          rename_i a
          have range : 0 ≤ a ∧ a < (2^64 : Int) := by norm_num; omega
          let v : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore a.toNat (by norm_num; omega)
          have vv : (v.val : Int) = a := by simp [v, Int.toNat_of_nonneg range.1]
          have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer a) = .ok v := by
            have encoded : Lynx.Rustler.encodeUnsigned v = .integer a := by simp [Lynx.Rustler.encodeUnsigned, vv]
            rw [← encoded]
            exact Lynx.Rustler.decodeUnsigned_encodeUnsigned v
          have nonzero : v ≠ 0#u64 := by
            intro eq
            have zero := (Aeneas.Std.UScalar.eq_equiv _ _).mp eq
            change v.val = 0 at zero
            omega
          have checked := Validated.Properties.validation_spec (.integer a) v decoded
          simp_all [«#{target}_positive:ensures/1», Elixir.#{native}.«#{target}/1»,
            Elixir.#{native}.«#{target}:execution/1», Validated.Properties.decoder_spec,
            Validated.Properties.flag_spec, Validated.Properties.result_spec,
            Lynx.Rustler.decodeTerm, Lynx.Rustler.Decoding.withDecoded_ok,
            Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
          \"\"\"
        law #{target}_rejects_zero,
          expects: (try do
            #{native}.#{target}(0) == :unexpected
          catch
            :error, :badarg -> true
          end),
          proof: ~LEAN\"\"\"
          simp [«#{target}_rejects_zero:ensures/0», Elixir.#{native}.«#{target}/1»,
            Elixir.#{native}.«#{target}:execution/1», Validated.Properties.decoder_spec,
            Validated.Properties.result_spec, Validated.Properties.zero_rejected,
            Lynx.Rustler.decodeTerm, Lynx.Rustler.Decoding.withDecoded_error,
            Lynx.Exception.classTerm, Lynx.Exception.reason]
          \"\"\"
        """
      end

    """
    defmodule LynxValidated#{suffix}.Laws do
      @compile :debug_info
      use Lynx.Laws
      #{laws}
    end
    """
  end
end
