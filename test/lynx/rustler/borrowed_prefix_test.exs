defmodule Lynx.Rustler.BorrowedPrefixTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for borrowed prefix NIF proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    @tag rustler: version
    test "verifies borrowed payload bounds through Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      prefix = "LynxBorrowedPrefix" <> String.replace(version, ".", "")
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
      File.mkdir_p!(Path.join(project, "BorrowedPrefix"))
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        cargo: [features: ["borrowed-prefix"]],
        only: [prefix_length: 2],
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "BorrowedPrefix.Extraction"
      ]

      discovered = Lynx.Rustler.prepare!(options)

      assert [%{"name" => "prefix_length", "arity" => 2, "flags" => 1} = binding] =
               discovered.bindings.bindings

      proof =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/BorrowedPrefix.lean"))
        |> String.replace("__FACADE__", binding["lean_name"])

      property = Path.join(project, "BorrowedPrefix/Properties.lean")
      File.write!(property, proof)

      options =
        options ++
          [
            proof_modules: ["BorrowedPrefix.Properties"],
            required_properties:
              Enum.map(
                ~w(core_spec bytes_spec caller_spec facade_spec),
                &("BorrowedPrefix.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :cross_crate_contract and
                   &1.theorem == "BorrowedPrefix.Properties.caller_spec" and
                   "BorrowedPrefix.Properties.core_spec" in &1.contracts_used)
             )

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "safe slice model")
             )

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "unverified FFI boundary")
             )

      library = Path.join(tmp, "borrowed_prefix")
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

      for {value, length, expected} <- [
            {<<>>, 0, 0},
            {<<>>, 1, nil},
            {<<>>, 256, 0},
            {<<65>>, 257, 1},
            {:binary.copy(<<255>>, 255), 4_294_967_295, 255},
            {<<0, 255, 128>>, 2, 2},
            {<<0, 255, 128>>, 3, 3},
            {<<0, 255, 128>>, 4, nil},
            {:binary.copy(<<255>>, 255), 255, 255}
          ],
          do: assert(apply(module, :prefix_length, [value, length]) == expected)

      for bad <- [-1, 4_294_967_296, true, "1"],
          do: assert(catch_error(apply(module, :prefix_length, [<<>>, bad])) == :badarg)

      for bad <- [-1, true, [1], <<1::size(1)>>],
          do: assert(catch_error(apply(module, :prefix_length, [bad, 0])) == :badarg)

      [{_, beam}] = Code.compile_string(laws(prefix))
      export = Path.join(tmp, "borrowed-prefix.export")
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
      core = Path.join(workspace, "core/src/protocol.rs")
      original = File.read!(core)
      changed = String.replace(original, "input.get(..length as usize)", "input.get(..0)")
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
      for {name, comparison, result} <- [
            {"available", "length <= byte_size(value)", "length"},
            {"truncated", "length > byte_size(value)", "nil"}
          ] do
        """
        law #{name}(value, length),
          requires: is_binary(value) and byte_size(value) <= 2_147_483_647 and
            is_integer(length) and length >= 0 and length <= 255 and #{comparison},
          expects: #{prefix}.Native.prefix_length(value, length) == #{result},
          proof: ~LEAN\"\"\"
          cases length <;> simp [«#{name}:requires/2», Erlang.erlang.«is_integer/1»] at requires
          rename_i n
          cases value <;> simp [«#{name}:requires/2», Erlang.erlang.«is_binary/1»] at requires
          rename_i bytes bits valid
          rcases bits with ⟨bits, bound⟩
          cases bits <;> simp_all [«#{name}:requires/2», Erlang.erlang.«is_binary/1»,
            Erlang.erlang.«byte_size/1»]
          have unsigned : bytes.size ≤ Aeneas.Std.Usize.max := by
            cases System.Platform.numBits_eq <;> scalar_tac
          have signed : bytes.size ≤ Aeneas.Std.Isize.max.toNat := by
            cases System.Platform.numBits_eq <;> scalar_tac
          let v : Aeneas.Std.U8 := Aeneas.Std.U8.ofNatCore n.toNat (by norm_num; omega)
          have vv : (v.val : Int) = n := by simp [v]; omega
          have range : 0 ≤ n ∧ n < (2^32 : Int) := by norm_num; omega
          have decoded : Lynx.Rustler.decodeUnsigned .U8 32 (.integer n) = .ok v := by
            simp only [Lynx.Rustler.decodeUnsigned]
            rw [if_pos range]
            apply congrArg Except.ok
            apply Aeneas.Std.UScalar.eq_of_val_eq
            dsimp only [v]
            rw [Aeneas.Std.U8.ofNatCore_val_eq]
            change n.toNat % 256 = n.toNat
            exact Nat.mod_eq_of_lt (by omega)
          have chosen : #{if name == "available", do: "v.val ≤ bytes.size", else: "¬ v.val ≤ bytes.size"} := by omega
          have cast_value : ((Aeneas.Std.UScalar.cast .U64 v).val : Int) = n := by
            rw [Aeneas.Std.UScalar.cast_val_mod_pow_greater_numBits_eq .U64 v (by decide)]
            exact vv
          have computed := BorrowedPrefix.Properties.facade_spec bytes v unsigned signed
          simp [«#{name}:ensures/2», Elixir.#{prefix}.Native.«prefix_length/2»,
            Elixir.#{prefix}.Native.«prefix_length:execution/2», Lynx.Rustler.decodeBinary,
            decoded, computed, chosen, cast_value, vv, Lynx.Rustler.execute, Lynx.Rustler.encodeOption,
            Lynx.Rustler.encodeUnsigned,
            Erlang.erlang.«==/2»]
          \"\"\"
        """
      end

    """
    defmodule #{prefix}.Laws do
      @compile :debug_info
      use Lynx.Laws
      #{Enum.join(laws, "\n")}
      law narrows_count,
        expects: #{prefix}.Native.prefix_length(<<>>, 256) == 0,
        proof: ~LEAN\"\"\"
        have decoded : Lynx.Rustler.decodeUnsigned .U8 32 (.integer 256) = .ok (0#u8) := rfl
        have computed := BorrowedPrefix.Properties.facade_spec (⟨#[]⟩ : ByteArray) (0#u8)
          (Nat.zero_le _) (Nat.zero_le _)
        norm_num [«narrows_count:ensures/0», Elixir.#{prefix}.Native.«prefix_length/2»,
          Elixir.#{prefix}.Native.«prefix_length:execution/2», Lynx.Rustler.decodeBinary,
          decoded, computed, Lynx.Rustler.execute,
          Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
        \"\"\"
      law rejects_count,
        expects: (try do
          #{prefix}.Native.prefix_length(<<>>, 4_294_967_296)
          false
        catch
          :error, :badarg -> true
        end),
        proof: ~LEAN\"\"\"
        simp [«rejects_count:ensures/0», Elixir.#{prefix}.Native.«prefix_length/2»,
          Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
      law rejects_partial_byte,
        expects: (try do
          #{prefix}.Native.prefix_length(<<1::size(1)>>, 0)
          false
        catch
          :error, :badarg -> true
        end),
        proof: ~LEAN\"\"\"
        simp [«rejects_partial_byte:ensures/0», Elixir.#{prefix}.Native.«prefix_length/2»,
          Lynx.Rustler.decodeBinary, Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
    end
    """
  end
end
