defmodule Lynx.Rustler.DecoderTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR or LYNX_AENEAS_DIR for Decoder proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "proves the actual custom Decoder with Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = String.replace(version, ".", "")
      native_module = "LynxDecoded#{suffix}.Native"
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
          ("#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
             source)
          |> String.replace("fn decoded_flag(", "#[verify::start_from]\nfn decoded_flag(")
          |> String.replace(
            "pub fn decode_flag_via(",
            "#[verify::start_from]\npub fn decode_flag_via("
          )
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
      File.mkdir_p!(Path.join(project, "Decoded"))
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
        cargo: [features: ["custom-decoder"]],
        only: [decoded_flag: 2],
        proof_roots: ["experiment_nif::decode_flag_via"],
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "Decoded.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)

      assert [
               %{"name" => "decoded_flag", "arity" => 2, "arguments" => [argument, "bool"]} =
                 binding
             ] = prepared.bindings.bindings

      assert %{"decoder" => decoder, "decoder_definition_id" => decoder_id} = argument
      property = Path.join(project, "Decoded/Properties.lean")

      properties =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/Decoded.lean"))
        |> String.replace("__DECODER__", decoder)
        |> String.replace("__IMPLEMENTATION__", binding["lean_name"])

      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["Decoded.Properties"],
            required_properties:
              Enum.map(
                ~w(invert_spec restore_spec decoder_success decoder_error decoder_range generic_flag_spec generic_flag_success facade_spec),
                &("Decoded.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :cross_crate_contract and
                   &1.theorem == "Decoded.Properties.restore_spec")
             )

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :rust_implementation and
                   &1.theorem == "Decoded.Properties.decoder_success")
             )

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "u64 Decoder FFI")
             )

      internal =
        Enum.find(
          prepared.extraction.translation["functions"],
          &(&1["rust_name"] == "experiment_nif::decode_flag_via")
        )

      assert decoder_id in prepared.extraction.audit.trait_dependencies[internal["def_id"]]

      refute Enum.any?(prepared.bindings.exports, fn {name, _, _} -> name == "decode_flag_via" end)

      missing = %{
        prepared.extraction.audit
        | functions:
            Enum.reject(prepared.extraction.audit.functions, &(&1["def_id"] == decoder_id))
      }

      assert_raise ArgumentError, ~r/missing, opaque or mismatched.*Decoder/, fn ->
        Lynx.Rustler.Bindings.link!(prepared.bindings, missing, prepared.extraction.translation)
      end

      library = Path.join(tmp, "decoded_native")
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

      for {value, expected} <- [{0, false}, {1, true}, {18_446_744_073_709_551_615, true}],
          do: assert(apply(native_atom, :decoded_flag, [value, false]) == expected)

      for value <- [-1, 18_446_744_073_709_551_616, :invalid],
          panic <- [false, true],
          do:
            assert_raise(ArgumentError, fn ->
              apply(native_atom, :decoded_flag, [value, panic])
            end)

      assert catch_error(apply(native_atom, :decoded_flag, [1, true])) == :nif_panicked
      assert_raise ArgumentError, fn -> apply(native_atom, :decoded_flag, [1, :invalid]) end
      [{_, beam}] = Code.compile_string(laws(native_module, suffix))
      export = Path.join(tmp, "decoder.export")
      reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
      stable_options = [lean_project: project, externals: [prepared.external]]
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
            "private axiom decoderTrust : False",
            "private theorem unfinishedDecoder : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      File.write!(property, properties)
      changed = String.replace(source, "enabled: value != 0", "enabled: value == 0")
      refute changed == source
      File.write!(native, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      constructed =
        String.replace(
          source,
          "Err(error) => Err(error)",
          "Err(_) => Err(rustler::Error::RaiseAtom(\"λ\"))"
        )

      refute constructed == source
      File.write!(native, constructed)

      assert_raise CompileError, ~r/Rustler RaiseAtom requires a validated ASCII literal/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(native, source)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end

  defp laws(native, suffix) do
    """
    defmodule LynxDecoded#{suffix}.Laws do
      @compile :debug_info
      use Lynx.Laws
      law nonzero(value),
        requires: is_integer(value) and value >= 0 and value <= 18_446_744_073_709_551_615,
        expects: #{native}.decoded_flag(value, false) == if(value == 0, do: false, else: true),
        proof: ~LEAN\"\"\"
        cases value <;> simp [«nonzero:requires/1», Erlang.erlang.«is_integer/1»] at requires
        rename_i a
        have range : 0 ≤ a ∧ a < (2^64 : Int) := by norm_num; omega
        let v : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore a.toNat (by norm_num; omega)
        have vv : (v.val : Int) = a := by simp [v, Int.toNat_of_nonneg range.1]
        have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer a) = .ok v := by
          have encoded : Lynx.Rustler.encodeUnsigned v = .integer a := by simp [Lynx.Rustler.encodeUnsigned, vv]
          rw [← encoded]
          exact Lynx.Rustler.decodeUnsigned_encodeUnsigned v
        have zero : v = 0#u64 ↔ a = 0 := by
          rw [Aeneas.Std.UScalar.eq_equiv]
          change v.val = 0 ↔ a = 0
          omega
        have conversion := Decoded.Properties.decoder_success (.integer a) v decoded
        by_cases az : a = 0 <;>
          simp_all [«nonzero:ensures/1», Elixir.#{native}.«decoded_flag/2»,
            Elixir.#{native}.«decoded_flag:execution/2»,
            Lynx.Rustler.Decoding.withDecoded_ok, Lynx.Rustler.decodeBool,
            Decoded.Properties.facade_spec, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
        \"\"\"
      law rejects_before_panic,
        expects: (try do
          #{native}.decoded_flag(:invalid, true) == :unexpected
        catch
          :error, :badarg -> true
        end),
        proof: ~LEAN\"\"\"
        have rejected : Lynx.Rustler.decodeUnsigned .U64 64 (.atom "invalid") =
            .error (.error (.atom "badarg")) := rfl
        simp [«rejects_before_panic:ensures/0», Elixir.#{native}.«decoded_flag/2»,
          Decoded.Properties.decoder_error _ _ rejected, Lynx.Rustler.Decoding.withDecoded_error,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
      law rejects_range,
        expects: (try do
          #{native}.decoded_flag(18_446_744_073_709_551_616, true) == :unexpected
        catch
          :error, :badarg -> true
        end),
        proof: ~LEAN\"\"\"
        have outside : ¬ (0 ≤ (18446744073709551616 : Int) ∧ (18446744073709551616 : Int) < 2^64) := by norm_num
        simp [«rejects_range:ensures/0», Elixir.#{native}.«decoded_flag/2»,
          Decoded.Properties.decoder_range (18446744073709551616 : Int) outside, Lynx.Rustler.Decoding.withDecoded_error,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
      law catches_panic,
        expects: (try do
          #{native}.decoded_flag(0, true) == :unexpected
        catch
          :error, :nif_panicked -> true
        end),
        proof: ~LEAN\"\"\"
        have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 0) = .ok 0#u64 := by
          have encoded : Lynx.Rustler.encodeUnsigned (0#u64) = .integer 0 := by simp [Lynx.Rustler.encodeUnsigned]
          rw [← encoded]
          exact Lynx.Rustler.decodeUnsigned_encodeUnsigned 0#u64
        simp [«catches_panic:ensures/0», Elixir.#{native}.«decoded_flag/2»,
          Elixir.#{native}.«decoded_flag:execution/2», Decoded.Properties.decoder_success _ _ decoded,
          Lynx.Rustler.Decoding.withDecoded_ok, Lynx.Rustler.decodeBool,
          Decoded.Properties.facade_spec, Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
    end
    """
  end
end
