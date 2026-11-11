defmodule Lynx.Rustler.DerivedTaggedDecoderTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_JOIN_RECOVERY_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  if is_nil(@tools),
    do:
      @moduletag(
        skip:
          "set LYNX_JOIN_RECOVERY_AENEAS_DIR with branch duplication for tagged Decoder proofs"
      )

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "proves actual tagged decoding and NIF laws on Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      prefix = "LynxDerivedTaggedDecode" <> String.replace(version, ".", "")
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

      native = Path.join(workspace, "nif/src/lib.rs")
      source = String.replace(File.read!(native), "LynxRustFixture.Native", prefix <> ".Native")
      File.write!(native, source)
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
      File.mkdir_p!(Path.join(project, "TaggedDecode"))
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        cargo: [features: ["derived-tagged-decoder"]],
        only: [normalised_reply: 1],
        branching: :duplicate,
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "TaggedDecode.Extraction"
      ]

      discovered = Lynx.Rustler.prepare!(options)
      [binding] = discovered.bindings.bindings
      assert %{"name" => "normalised_reply", "arity" => 1} = binding

      proof =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/DerivedTaggedDecoder.lean"))
        |> String.replace("__FACADE__", binding["lean_name"])

      property = Path.join(project, "TaggedDecode/Properties.lean")
      File.write!(property, proof)

      options =
        options ++
          [
            proof_modules: ["TaggedDecode.Properties"],
            required_properties:
              Enum.map(
                ~w(core_spec caller_spec decoder_success facade_spec encoder_spec unknown_atom empty_tuple field_error_callback field_error),
                &("TaggedDecode.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :nif_adapter and &1.status == :verified)
             )

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :rust_implementation and
                   &1.theorem == "TaggedDecode.Properties.decoder_success")
             )

      assert Enum.any?(
               prepared.verification.guarantees,
               &(&1.kind == :cross_crate_contract and
                   &1.theorem == "TaggedDecode.Properties.caller_spec")
             )

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "Copy Ok payloads")
             )

      library = Path.join(tmp, "tagged_native")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {name, arity, _} <- Lynx.Rustler.Metadata.inspect!(prepared.library).exports do
          "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"
        end

      [{native_module, _}] =
        Code.compile_string("""
        defmodule #{prefix}.Native do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
          #{Enum.join(stubs, "\n")}
        end
        """)

      assert apply(native_module, :normalised_reply, [:empty]) == :empty
      assert apply(native_module, :normalised_reply, [{:equal, 7}]) == {:equal, 7}
      assert apply(native_module, :normalised_reply, [{:ordered, 9, 4}]) == {:ordered, 4, 9}

      for input <- [:unknown, {}, {1, 2}] do
        assert catch_error(apply(native_module, :normalised_reply, [input])) == :invalid_variant
      end

      for bad <- [-1, 18_446_744_073_709_551_616, true, "1"] do
        assert catch_error(apply(native_module, :normalised_reply, [{:equal, bad}])) ==
                 "Could not decode field on position 1"
      end

      [{_, beam}] = Code.compile_string(laws(prefix))
      export = Path.join(tmp, "tagged-decoder.export")
      law_options = [native: {Lynx.Rustler, options}, export: export]
      reports = Lynx.Laws.verify([beam], law_options)

      assert Enum.all?(reports, &(&1.status == :ok)),
             inspect(for r <- reports, r.status != :ok, do: Map.take(r, [:module, :diagnostics]))

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      # Rustler's generated atom-cache field order can change on recompilation.
      # Cache reuse requires one fixed, validated extraction, consumed before
      # another preparation replaces its imported implementations.
      cached_bundle = Lynx.Rustler.prepare!(options)
      stable_options = [externals: [cached_bundle.external], lean_project: project]
      checked = Lynx.Laws.verify([beam], stable_options)
      assert Enum.all?(checked, &(&1.status == :ok))
      warm = Lynx.Laws.verify([beam], stable_options)

      assert Enum.all?(warm, &(&1.status == :ok and &1.cached)),
             inspect(Enum.map(warm, &Map.take(&1, [:module, :status, :cached, :diagnostics])),
               limit: :infinity
             )

      for extra <- [
            "private axiom unjustifiedTag : False",
            "private theorem unfinishedTag : True := by sorry"
          ] do
        File.write!(property, proof <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      File.write!(
        property,
        proof <>
          """
          theorem wrong_tag_contract : experiment_nif.OrderedReply.Insts.RustlerTypesDecoder.decode (.atom "unknown") =
              Aeneas.Std.RustM.ok (.Ok experiment_nif.OrderedReply.Empty) := by
            rw [TaggedDecode.Properties.unknown_atom "unknown" (by decide)]
          """
      )

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(property, proof)
      core = Path.join(workspace, "core/src/lib.rs")
      original = File.read!(core)
      changed = String.replace(original, "if left <= right", "if left >= right")
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
    ~S'''
    defmodule LynxDerivedTaggedDecode.Laws do
      @compile :debug_info
      use Lynx.Laws
      law preserves_empty,
        expects: LynxDerivedTaggedDecode.Native.normalised_reply(:empty) == :empty,
        proof: ~LEAN"""
        simp [«preserves_empty:ensures/0», Elixir.LynxDerivedTaggedDecode.Native.«normalised_reply/1»,
          Elixir.LynxDerivedTaggedDecode.Native.«normalised_reply:execution/1», TaggedDecode.Properties.decoder_empty,
          TaggedDecode.Properties.facade_spec, TaggedDecode.Properties.normalise, TaggedDecode.Properties.encoder_spec,
          TaggedDecode.Properties.replyTerm, Lynx.Rustler.Decoding.withDecoded, Lynx.Rustler.execute, Erlang.erlang.«==/2»]
        """
      law orders_tagged_fields(left, right),
        requires: is_integer(left) and is_integer(right) and left >= 0 and right >= 0 and
          left <= 18_446_744_073_709_551_615 and right <= 18_446_744_073_709_551_615,
        expects: :erlang.element(2, LynxDerivedTaggedDecode.Native.normalised_reply({:ordered, left, right})) == if(left <= right, do: left, else: right),
        proof: ~LEAN"""
        cases left <;> cases right <;>
          simp [«orders_tagged_fields:requires/2», Erlang.erlang.«is_integer/1»] at requires
        rename_i a b
        have arange : 0 ≤ a ∧ a < (2^64 : Int) := by norm_num; omega
        have brange : 0 ≤ b ∧ b < (2^64 : Int) := by norm_num; omega
        let l : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore a.toNat (by norm_num; omega)
        let r : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore b.toNat (by norm_num; omega)
        have lv : (l.val : Int) = a := by simp only [l, Aeneas.Std.U64.ofNatCore, Aeneas.Std.UScalar.ofNatCore_val_eq, Int.toNat_of_nonneg arange.1]
        have rv : (r.val : Int) = b := by simp only [r, Aeneas.Std.U64.ofNatCore, Aeneas.Std.UScalar.ofNatCore_val_eq, Int.toNat_of_nonneg brange.1]
        have decoded : experiment_nif.OrderedReply.Insts.RustlerTypesDecoder.decode
            (.tuple #[.atom "ordered", .integer a, .integer b]) = Aeneas.Std.RustM.ok (.Ok (.Ordered l r)) := by
          simpa only [TaggedDecode.Properties.replyTerm, Lynx.Rustler.encodeUnsigned, lv, rv] using
            TaggedDecode.Properties.decoder_ordered l r
        by_cases ordered : a ≤ b
        · have rust_ordered : l ≤ r := by change l.val ≤ r.val; omega
          simp [«orders_tagged_fields:ensures/2», Elixir.LynxDerivedTaggedDecode.Native.«normalised_reply/1»,
            Elixir.LynxDerivedTaggedDecode.Native.«normalised_reply:execution/1», decoded, rust_ordered,
            TaggedDecode.Properties.facade_spec, TaggedDecode.Properties.normalise, TaggedDecode.Properties.encoder_spec,
            TaggedDecode.Properties.replyTerm, Lynx.Rustler.Decoding.withDecoded, Lynx.Rustler.execute,
            Lynx.Rustler.encodeUnsigned, lv, rv, ordered, Int.isLE_compare, Erlang.erlang.«element/2», Erlang.erlang.«==/2»]
        · have rust_ordered : ¬ l ≤ r := by change ¬ l.val ≤ r.val; omega
          simp [«orders_tagged_fields:ensures/2», Elixir.LynxDerivedTaggedDecode.Native.«normalised_reply/1»,
            Elixir.LynxDerivedTaggedDecode.Native.«normalised_reply:execution/1», decoded, rust_ordered,
            TaggedDecode.Properties.facade_spec, TaggedDecode.Properties.normalise, TaggedDecode.Properties.encoder_spec,
            TaggedDecode.Properties.replyTerm, Lynx.Rustler.Decoding.withDecoded, Lynx.Rustler.execute,
            Lynx.Rustler.encodeUnsigned, lv, rv, ordered, Int.isLE_compare, Erlang.erlang.«element/2», Erlang.erlang.«==/2»]
        """
    end
    '''
    |> String.replace("LynxDerivedTaggedDecode", prefix)
  end
end
