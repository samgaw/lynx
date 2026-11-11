defmodule Lynx.Rustler.ScalarCallbacksTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for scalar callback NIF proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "composes captured scalar callbacks through Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      prefix = "LynxScalarCapture" <> String.replace(version, ".", "")
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

      native = Path.join(workspace, "nif/src/lib.rs")

      File.write!(
        native,
        String.replace(File.read!(native), "LynxRustFixture.Native", prefix <> ".Native")
      )

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
      File.mkdir_p!(Path.join(project, "ScalarCapture"))
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        cargo: [features: ["scalar-callbacks"]],
        only: [masked_error: 2],
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "ScalarCapture.Extraction"
      ]

      discovered = Lynx.Rustler.prepare!(options)

      assert [%{"name" => "masked_error", "arity" => 2, "flags" => 1} = binding] =
               discovered.bindings.bindings

      proof =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/ScalarCaptures.lean"))
        |> String.replace("__FACADE__", binding["lean_name"])

      property = Path.join(project, "ScalarCapture/Properties.lean")
      File.write!(property, proof)

      options =
        options ++
          [
            proof_modules: ["ScalarCapture.Properties"],
            required_properties:
              Enum.map(
                ~w(core_spec caller_spec facade_spec zero_spec self_spec),
                &("ScalarCapture.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :cross_crate_contract and
                   &1.theorem == "ScalarCapture.Properties.caller_spec")
             )

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "scalar captures")
             )

      library = Path.join(tmp, "scalar_capture")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {name, arity, _} <- prepared.bindings.exports,
            do:
              "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      [{module, _}] =
        Code.compile_string("""
        defmodule #{prefix}.Native do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
          #{Enum.join(stubs, "\n")}
        end
        """)

      for {value, mask} <- [{0, 7}, {7, 0}, {7, 7}, {18_446_744_073_709_551_615, 42}],
          do:
            assert(
              apply(module, :masked_error, [value, mask]) == {:error, Bitwise.bxor(value, mask)}
            )

      for bad <- [-1, 18_446_744_073_709_551_616, true, "1"] do
        assert catch_error(apply(module, :masked_error, [bad, 0])) == :badarg
        assert catch_error(apply(module, :masked_error, [0, bad])) == :badarg
      end

      [{_, beam}] = Code.compile_string(laws(prefix))
      export = Path.join(tmp, "scalar-captures.export")
      reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)

      assert Enum.all?(reports, &(&1.status == :ok)),
             inspect(for r <- reports, r.status != :ok, do: Map.take(r, [:module, :diagnostics]))

      for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
          do:
            assert(
              Enum.any?(Enum.flat_map(reports, &Map.get(&1, :guarantees, [])), &(&1.kind == kind))
            )

      warm = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})

      assert Enum.all?(warm, &(&1.status == :ok and &1.cached)),
             inspect(Enum.map(warm, &Map.take(&1, [:module, :status, :cached])))

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
      core = Path.join(workspace, "core/src/lib.rs")
      original = File.read!(core)
      changed = String.replace(original, "error ^ mask", "error | mask")
      refute changed == original
      File.write!(core, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(core, original)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end

  defp laws(prefix) do
    laws =
      for {name, mask, result, theorem} <- [
            {"zero", "0", "value", "zero_spec"},
            {"self", "value", "0", "self_spec"}
          ] do
        """
        law #{name}(value),
          requires: is_integer(value) and value >= 0 and value <= 18_446_744_073_709_551_615,
          expects: #{prefix}.Native.masked_error(value, #{mask}) == {:error, #{result}},
          proof: ~LEAN\"\"\"
          cases value <;> simp [«#{name}:requires/1», Erlang.erlang.«is_integer/1»] at requires
          rename_i n
          have range : 0 ≤ n ∧ n < (2^64 : Int) := by norm_num; omega
          let v : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore n.toNat (by norm_num; omega)
          have vv : (v.val : Int) = n := by simp [v, Int.toNat_of_nonneg range.1]
          have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer n) = .ok v := by
            have encoded : Lynx.Rustler.encodeUnsigned v = .integer n := by simp [Lynx.Rustler.encodeUnsigned, vv]
            rw [← encoded]
            exact Lynx.Rustler.decodeUnsigned_encodeUnsigned v
          have zero_decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 0) = .ok (0#u64) := by
            simpa [Lynx.Rustler.encodeUnsigned] using Lynx.Rustler.decodeUnsigned_encodeUnsigned (0#u64)
          simp [«#{name}:ensures/1», Elixir.#{prefix}.Native.«masked_error/2»,
            Elixir.#{prefix}.Native.«masked_error:execution/2», decoded, zero_decoded,
            ScalarCapture.Properties.#{theorem}, Lynx.Rustler.execute, Lynx.Rustler.encodeResult,
            Lynx.Rustler.encodeUnsigned, vv, Erlang.erlang.«==/2»]
          \"\"\"
        """
      end

    """
    defmodule #{prefix}.Laws do
      @compile :debug_info
      use Lynx.Laws
      #{Enum.join(laws, "\n")}
    end
    """
  end
end
