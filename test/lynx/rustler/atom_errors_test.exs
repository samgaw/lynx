defmodule Lynx.Rustler.AtomErrorsTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR or LYNX_AENEAS_DIR for atom error proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "proves actual Rustler atom error conversion with Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = String.replace(version, ".", "")
      native_module = "LynxAtomErrors#{suffix}.Native"
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
      File.mkdir_p!(Path.join(project, "Atoms"))
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
        cargo: [features: ["atom-errors"]],
        only: [validated_result: 1, validated_flag: 1],
        mir: nil,
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "Atoms.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)
      by_name = Map.new(prepared.bindings.bindings, &{&1["name"], &1})
      [argument] = by_name["validated_flag"]["arguments"]
      assert %{"decoder" => decoder} = argument

      assert %{values: %{entries: entries, sites: sites}} =
               prepared.extraction.rustler_constructors

      assert Enum.sort(Enum.map(sites, & &1.variant)) == ["Atom", "RaiseAtom"]

      literal = fn variant ->
        entry = Enum.find(entries, &(&1.variant == variant))
        "Atoms.Extraction.ErrorConstants.literal_#{entry.index}"
      end

      properties =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/Atoms.lean"))
        |> String.replace("__ATOM__", literal.("Atom"))
        |> String.replace("__RAISE__", literal.("RaiseAtom"))
        |> String.replace("__DECODER__", decoder)
        |> String.replace("__FLAG__", by_name["validated_flag"]["lean_name"])
        |> String.replace("__RESULT__", by_name["validated_result"]["lean_name"])

      property = Path.join(project, "Atoms/Properties.lean")
      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["Atoms.Properties"],
            required_properties:
              Enum.map(
                ~w(invert_spec restore_spec validation_spec validation_error decoder_spec flag_spec result_spec zero_rejected raising_spec raising_error zero_raised),
                &("Atoms.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :rust_implementation and
                   &1.theorem == "Atoms.Properties.validation_spec")
             )

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :cross_crate_contract and
                   &1.theorem == "Atoms.Properties.restore_spec")
             )

      assert Enum.any?(prepared.verification.unverified_external_calls, fn model ->
               String.contains?(model.rust_name, "Literal") and
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

        for value <- [-1, 18_446_744_073_709_551_616, :invalid],
            do: assert_raise(ArgumentError, fn -> apply(native_atom, name, [value]) end)
      end

      assert apply(native_atom, :validated_flag, [0]) == :zero
      assert catch_error(apply(native_atom, :validated_result, [0])) == :zero

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

      wrong = String.replace(properties, ".atom \"zero\"", ".atom \"wrong\"")
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

      # Static SDK errors have explicit modeled destruction. Discarding the
      # original zero Atom in favor of BadArg must still fail error preservation.
      discarded =
        String.replace(
          source,
          "Err(error) => Err(error)",
          "Err(_) => Err(rustler::Error::BadArg)"
        )

      refute discarded == source
      File.write!(native, discarded)

      failure =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rustler.prepare!(options)
        end

      assert Exception.message(failure) =~ "unsolved goals"

      File.write!(native, source)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end

  defp laws(native, suffix) do
    positive =
      for target <- ~w(validated_flag validated_result), into: "" do
        property = if target == "validated_flag", do: "validation_spec", else: "raising_spec"

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
          have checked := Atoms.Properties.#{property} (.integer a) v decoded
          simp_all [«#{target}_positive:ensures/1», Elixir.#{native}.«#{target}/1»,
            Elixir.#{native}.«#{target}:execution/1», Atoms.Properties.decoder_spec,
            Atoms.Properties.flag_spec, Atoms.Properties.result_spec,
            Lynx.Rustler.decodeTerm, Lynx.Rustler.Decoding.withDecoded_ok,
            Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
          \"\"\"
        """
      end

    """
    defmodule LynxAtomErrors#{suffix}.Laws do
      @compile :debug_info
      use Lynx.Laws
      #{positive}
      law atom_returned,
        expects: #{native}.validated_flag(0) == :zero,
        proof: ~LEAN\"\"\"
        simp [«atom_returned:ensures/0», Elixir.#{native}.«validated_flag/1»,
          Elixir.#{native}.«validated_flag:execution/1», Atoms.Properties.decoder_spec,
          Atoms.Properties.zero_rejected, Lynx.Rustler.Decoding.withDecoded_error,
          Erlang.erlang.«==/2»]
        \"\"\"
      law atom_raised,
        expects: (try do
          #{native}.validated_result(0) == :unexpected
        catch
          :error, :zero -> true
        end),
        proof: ~LEAN\"\"\"
        simp [«atom_raised:ensures/0», Elixir.#{native}.«validated_result/1»,
          Elixir.#{native}.«validated_result:execution/1», Atoms.Properties.result_spec,
          Atoms.Properties.zero_raised, Lynx.Rustler.decodeTerm,
          Lynx.Rustler.Decoding.withDecoded_error, Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
    end
    """
  end
end
