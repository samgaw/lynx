defmodule Lynx.Rustler.PayloadErrorsTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for deferred Encoder proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "proves deferred Rustler error payloads with Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = String.replace(version, ".", "")
      native_module = "LynxPayload#{suffix}.Native"
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for name <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
          do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))
      native = Path.join(workspace, "nif/src/lib.rs")
      source = String.replace(File.read!(native), "LynxRustFixture.Native", native_module)

      source =
        "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
          Enum.reduce(~w(boxed_error boxed_returned), source, fn name, s ->
            String.replace(s, "fn #{name}(", "#[verify::start_from]\nfn #{name}(")
          end)

      File.write!(native, source)

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "Payloads"))
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        root_attribute: "verify::start_from",
        cargo: [features: ["boxed-errors"]],
        only: [boxed_error: 2, boxed_term: 2],
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "Payloads.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)
      by_name = Map.new(prepared.bindings.bindings, &{&1["name"], &1})

      encoder =
        Enum.find(
          prepared.extraction.translation["functions"],
          &String.ends_with?(&1["rust_name"], "::encode")
        )["lean_name"]

      assert %{values: %{entries: entries}} = prepared.extraction.rustler_constructors
      assert Enum.sort(Enum.map(entries, & &1.variant)) == ["RaiseTerm", "Term"]

      properties =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/Payloads.lean"))
        |> String.replace("__ENCODER__", encoder)
        |> String.replace("__RAISED__", by_name["boxed_error"]["lean_name"])
        |> String.replace("__RETURNED__", by_name["boxed_term"]["lean_name"])

      property = Path.join(project, "Payloads/Properties.lean")
      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["Payloads.Properties"],
            required_properties:
              Enum.map(
                ~w(invert_spec restore_spec encoder_spec raised_constructed returned_constructed raised_spec returned_spec raised_panic returned_panic),
                &("Payloads.Properties." <> &1)
              )
          ]

      verified = Lynx.Rustler.prepare!(options)

      assert Enum.any?(
               verified.verification.guarantees,
               &(&1.kind == :rust_implementation &&
                   &1.theorem == "Payloads.Properties.encoder_spec")
             )

      assert Enum.any?(verified.verification.guarantees, &(&1.kind == :cross_crate_contract))

      assert Enum.any?(
               verified.verification.unverified_external_calls,
               &(String.contains?(&1.rust_name, "Payload") && &1.implementation_verified == false)
             )

      library = Path.join(tmp, "payload_native")
      File.cp!(verified.library, library <> ".so")

      stubs =
        for {name, arity, _} <- verified.bindings.exports,
            do:
              "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      [{native_atom, _}] =
        Code.compile_string("""
        defmodule #{native_module} do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(~c"#{library}",0)
          #{Enum.join(stubs, "\n")}
        end
        """)

      # Never invoke a panicking error Encoder: return conversion is outside the
      # macro's catch_unwind and can unwind through the native FFI boundary.
      for value <- [0, 1, 7, 18_446_744_073_709_551_615] do
        assert catch_error(apply(native_atom, :boxed_error, [value, false])) == value
        assert apply(native_atom, :boxed_term, [value, false]) == {:error, value}
      end

      for target <- [:boxed_error, :boxed_term],
          value <- [-1, 18_446_744_073_709_551_616, :invalid] do
        assert_raise ArgumentError, fn -> apply(native_atom, target, [value, false]) end
      end

      [{_, beam}] = Code.compile_string(laws(native_module, suffix))
      export = Path.join(tmp, "payload.export")
      reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

      assert Enum.all?(
               Lynx.Laws.verify([beam], lean_project: project, externals: [verified.external]),
               &(&1.status == :ok and &1.cached)
             )

      [{_, panic_beam}] = Code.compile_string(laws(native_module, suffix, :panic))

      refute Enum.all?(
               Lynx.Laws.verify([panic_beam],
                 lean_project: project,
                 externals: [verified.external]
               ),
               &(&1.status == :ok)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      for extra <- [
            "private axiom payloadTrust : False",
            "private theorem unfinishedPayload : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      wrong =
        String.replace(properties, ".integer input.value.val", ".integer (input.value.val + 1)")

      refute wrong == properties
      File.write!(property, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(property, properties)
      changed = String.replace(source, "encode(&self.value, env)", "encode(&0, env)")
      refute changed == source
      File.write!(native, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(native, source)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end

  defp laws(native, suffix, mode \\ :normal) do
    bindings =
      if mode == :panic,
        do: [{"boxed_error", "raised_panic"}],
        else: [{"boxed_error", "raised_spec"}, {"boxed_term", "returned_spec"}]

    module = if mode == :panic, do: "PanickingLaws", else: "Laws"

    laws =
      for {target, property} <- bindings,
          into: "" do
        expected =
          cond do
            mode == :panic ->
              "(try do #{native}.boxed_error(value,true) == :unexpected catch :error, :nif_panicked -> true end)"

            target == "boxed_error" ->
              "(try do #{native}.#{target}(value,false) == :unexpected catch :error, reason -> reason == value end)"

            true ->
              "#{native}.#{target}(value,false) == {:error,value}"
          end

        """
        law #{target}_value(value),
          requires: is_integer(value) and value >= 0 and value <= 18_446_744_073_709_551_615,
          expects: #{expected},
          proof: ~LEAN\"\"\"
          cases value <;> simp [«#{target}_value:requires/1», Erlang.erlang.«is_integer/1»] at requires
          rename_i a
          have range : 0 ≤ a ∧ a < (2^64 : Int) := by norm_num; omega
          let v : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore a.toNat (by norm_num; omega)
          have vv : (v.val : Int) = a := by simp [v, Int.toNat_of_nonneg range.1]
          have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer a) = .ok v := by
            have encoded : Lynx.Rustler.encodeUnsigned v = .integer a := by simp [Lynx.Rustler.encodeUnsigned, vv]
            rw [← encoded]
            exact Lynx.Rustler.decodeUnsigned_encodeUnsigned v
          have checked := Payloads.Properties.#{property} v
          simp_all [«#{target}_value:ensures/1», Elixir.#{native}.«#{target}/2»,
            Elixir.#{native}.«#{target}:execution/2», Lynx.Rustler.decodeBool,
            Erlang.erlang.«==/2», Lynx.Exception.classTerm, Lynx.Exception.reason]
          \"\"\"
        """
      end

    """
    defmodule LynxPayload#{suffix}.#{module} do
      @compile :debug_info
      use Lynx.Laws
      #{laws}
    end
    """
  end
end
