defmodule Lynx.Rustler.NifResultTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR or LYNX_AENEAS_DIR for NifResult proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "proves actual NifResult return conversion with Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = String.replace(version, ".", "")
      native_module = "LynxReturned#{suffix}.Native"
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
            Enum.reduce(~w(forwarded_result spelled_result echo_term), source, fn name, source ->
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
      File.mkdir_p!(Path.join(project, "Returned"))
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
        cargo: [features: ["nif-result"]],
        only: [forwarded_result: 2, explicit_result: 2, echo_term: 1],
        mir: nil,
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "Returned.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)
      by_name = Map.new(prepared.bindings.bindings, &{&1["name"], &1})

      assert %{
               "result" => %{"nif_result" => "bool"},
               "arguments" => ["term", "bool"],
               "flags" => 1
             } = by_name["explicit_result"]

      assert %{"result" => %{"nif_result" => "bool"}, "flags" => 0} = by_name["forwarded_result"]
      assert %{"result" => "term", "arguments" => ["term"]} = by_name["echo_term"]

      properties =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/Returned.lean"))
        |> String.replace("__ALIASED__", by_name["forwarded_result"]["lean_name"])
        |> String.replace("__SPELLED__", by_name["explicit_result"]["lean_name"])
        |> String.replace("__IDENTITY__", by_name["echo_term"]["lean_name"])

      property = Path.join(project, "Returned/Properties.lean")
      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["Returned.Properties"],
            required_properties:
              Enum.map(
                ~w(invert_spec restore_spec success rejected rejected_range aliased_spec spelled_spec identity_spec),
                &("Returned.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :cross_crate_contract and
                   &1.theorem == "Returned.Properties.restore_spec")
             )

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :rust_implementation and &1.theorem == "Returned.Properties.success")
             )

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "Opaque Rustler Error")
             )

      library = Path.join(tmp, "returned_native")
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

      for name <- [:forwarded_result, :explicit_result] do
        for {value, expected} <- [{0, false}, {1, true}, {18_446_744_073_709_551_615, true}],
            do: assert(apply(native_atom, name, [value, false]) == expected)

        for value <- [-1, 18_446_744_073_709_551_616, :invalid],
            panic <- [false, true],
            do: assert_raise(ArgumentError, fn -> apply(native_atom, name, [value, panic]) end)

        assert catch_error(apply(native_atom, name, [1, true])) == :nif_panicked
        assert_raise ArgumentError, fn -> apply(native_atom, name, [1, :invalid]) end
      end

      for term <- [
            nil,
            true,
            -1,
            1_267_650_600_228_229_401_496_703_205_376,
            <<0, 255>>,
            {1, :ok},
            %{a: [1, 2]}
          ],
          do: assert(apply(native_atom, :echo_term, [term]) === term)

      [{_, beam}] = Code.compile_string(laws(native_module, suffix))
      export = Path.join(tmp, "returned.export")
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
            "private axiom returnTrust : False",
            "private theorem unfinishedReturn : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      wrong = String.replace(properties, "value != 0#u64", "value == 0#u64")
      refute wrong == properties
      File.write!(property, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(property, properties)
      changed = String.replace(source, "restore(value != 0)", "restore(value == 0)")
      refute changed == source
      File.write!(native, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      constructed =
        String.replace(
          source,
          "Err(error) => Err(error)",
          "Err(_) => Err(rustler::Error::RaiseAtom(\"unsupported\"))"
        )

      File.write!(native, constructed)

      assert_raise CompileError, ~r/Rustler Error construction or inspection/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(native, source)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

      assert_raise ArgumentError, ~r/runtime Rustler NifResult/, fn ->
        Lynx.Rustler.prepare!(Keyword.put(options, :execution, :runtime))
      end
    end
  end

  defp laws(native, suffix) do
    successes =
      for target <- ~w(forwarded_result explicit_result), into: "" do
        spec = if target == "forwarded_result", do: "aliased_spec", else: "spelled_spec"

        """
        law #{target}_success(value),
          requires: is_integer(value) and value >= 0 and value <= 18_446_744_073_709_551_615,
          expects: #{native}.#{target}(value, false) == if(value == 0, do: false, else: true),
          proof: ~LEAN\"\"\"
          cases value <;> simp [«#{target}_success:requires/1», Erlang.erlang.«is_integer/1»] at requires
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
          have returned := Returned.Properties.success (.integer a) v false decoded
          by_cases az : a = 0 <;>
            simp_all [«#{target}_success:ensures/1», Elixir.#{native}.«#{target}/2»,
              Elixir.#{native}.«#{target}:execution/2», Returned.Properties.#{spec}, Lynx.Rustler.decodeTerm,
              Lynx.Rustler.decodeBool,
              Lynx.Rustler.Decoding.withDecoded_ok, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
          \"\"\"
        """
      end

    """
    defmodule LynxReturned#{suffix}.Laws do
      @compile :debug_info
      use Lynx.Laws
      #{successes}
      law raw_identity(value),
        expects: #{native}.echo_term(value) === value,
        proof: ~LEAN\"\"\"
        simp [«raw_identity:ensures/1», Elixir.#{native}.«echo_term/1»,
          Elixir.#{native}.«echo_term:execution/1», Returned.Properties.identity_spec,
          Lynx.Rustler.decodeTerm, Erlang.erlang.«=:=/2»]
        \"\"\"
      law rejects_range(value),
        requires: is_integer(value) and (value < 0 or value > 18_446_744_073_709_551_615),
        expects: (try do
          #{native}.forwarded_result(value, true) == :unexpected
        catch
          :error, :badarg -> true
        end),
        proof: ~LEAN\"\"\"
        cases value <;> simp [«rejects_range:requires/1», Erlang.erlang.«is_integer/1»] at requires
        rename_i a
        have outside : ¬ (0 ≤ a ∧ a < (2^64 : Int)) := by norm_num; omega
        simp [«rejects_range:ensures/1», Elixir.#{native}.«forwarded_result/2»,
          Elixir.#{native}.«forwarded_result:execution/2», Returned.Properties.aliased_spec,
          Returned.Properties.rejected_range a true outside, Lynx.Rustler.decodeTerm,
          Lynx.Rustler.decodeBool, Lynx.Rustler.Decoding.withDecoded_error,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
      law catches_panic,
        expects: (try do
          #{native}.explicit_result(0, true) == :unexpected
        catch
          :error, :nif_panicked -> true
        end),
        proof: ~LEAN\"\"\"
        have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 0) = .ok 0#u64 := by
          have encoded : Lynx.Rustler.encodeUnsigned (0#u64) = .integer 0 := by simp [Lynx.Rustler.encodeUnsigned]
          rw [← encoded]
          exact Lynx.Rustler.decodeUnsigned_encodeUnsigned 0#u64
        simp [«catches_panic:ensures/0», Elixir.#{native}.«explicit_result/2»,
          Elixir.#{native}.«explicit_result:execution/2», Returned.Properties.spelled_spec,
          Returned.Properties.success _ _ true decoded, Lynx.Rustler.decodeTerm,
          Lynx.Rustler.decodeBool, Lynx.Rustler.Decoding.withDecoded,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
    end
    """
  end
end
