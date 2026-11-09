defmodule Lynx.Rustler.DerivedTupleTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_PURE_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR or LYNX_AENEAS_DIR for derived Encoder proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "verifies the actual NifTuple Encoder under Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = if version == "0.39.0", do: "39", else: "38"
      native_module = "LynxDerived#{suffix}.Native"
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

      native = Path.join(workspace, "nif/src/lib.rs")

      original_native =
        String.replace(File.read!(native), "LynxRustFixture.Native", native_module)

      File.write!(native, original_native)
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
      property = Path.join(project, "RustWorkspace/DerivedTuple.lean")
      File.cp!(Path.join(@fixture, "proofs/RustWorkspace/DerivedTuple.lean"), property)

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "RustWorkspace.DerivedFacade",
        cargo: [features: ["derived-tuple"]],
        only: [derived_pair: 2],
        proof_modules: ["RustWorkspace.DerivedTuple"],
        required_properties:
          Enum.map(
            ~w(core_spec caller_spec ordered_fields facade_spec encoder_spec),
            &("RustWorkspace.DerivedTuple." <> &1)
          )
      ]

      prepared = Lynx.Rustler.prepare!(options)
      assert prepared.verification.rustler_version == version

      assert Enum.any?(prepared.verification.guarantees, fn evidence ->
               evidence.kind == :cross_crate_contract and
                 evidence.theorem == "RustWorkspace.DerivedTuple.caller_spec" and
                 "RustWorkspace.DerivedTuple.core_spec" in evidence.contracts_used
             end)

      assert Enum.any?(prepared.verification.guarantees, fn evidence ->
               evidence.kind == :rust_implementation and
                 evidence.theorem == "RustWorkspace.DerivedTuple.encoder_spec" and
                 String.ends_with?(evidence.file, "nif/src/lib.rs") and
                 String.contains?(evidence.rust_name, "OrderedFields")
             end)

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "tuple construction FFI model")
             )

      [binding] = prepared.bindings.bindings
      encoder_id = binding["result"]["encoder_definition_id"]

      missing = %{
        prepared.extraction.audit
        | functions:
            Enum.reject(prepared.extraction.audit.functions, &(&1["def_id"] == encoder_id))
      }

      assert_raise ArgumentError,
                   ~r/missing, opaque or mismatched first-party Rustler Encoder/,
                   fn ->
                     Lynx.Rustler.Bindings.link!(
                       prepared.bindings,
                       missing,
                       prepared.extraction.translation
                     )
                   end

      File.mkdir_p!(Path.join(workspace, "priv"))
      File.cp!(prepared.library, Path.join(workspace, "priv/libexperiment_nif.so"))

      stubs =
        for {name, arity, _} <- Lynx.Rustler.Metadata.inspect!(prepared.library).exports do
          arguments = Enum.join(List.duplicate("_", arity), ", ")
          "def #{name}(#{arguments}), do: :erlang.nif_error(:not_loaded)"
        end

      [{native_atom, _}] =
        Code.compile_string("""
        defmodule #{native_module} do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(~c"#{Path.join(workspace, "priv/libexperiment_nif")}", 0)
          #{Enum.join(stubs, "\n")}
        end
        """)

      for {left, right, expected} <- [
            {9, 4, {4, 9}},
            {4, 9, {4, 9}},
            {7, 7, {7, 7}},
            {0, 18_446_744_073_709_551_615, {0, 18_446_744_073_709_551_615}}
          ],
          do: assert(apply(native_atom, :derived_pair, [left, right]) == expected)

      for arguments <- [[-1, 0], [0, 18_446_744_073_709_551_616], [true, 0]],
          do: assert_raise(ArgumentError, fn -> apply(native_atom, :derived_pair, arguments) end)

      [{_, beam}] =
        Code.compile_string(
          String.replace(
            ~S'''
            defmodule __LAW__ do
              @compile :debug_info
              use Lynx.Laws
              law orders_fields(left, right),
                requires: is_integer(left) and is_integer(right) and left >= 0 and right >= 0 and
                  left <= 18_446_744_073_709_551_615 and right <= 18_446_744_073_709_551_615,
                expects: __NATIVE__.derived_pair(left, right) == if(left <= right, do: {left, right}, else: {right, left}),
                proof: ~LEAN"""
                cases left <;> cases right <;>
                  simp [«orders_fields:requires/2», Erlang.erlang.«is_integer/1»] at requires
                rename_i a b
                have arange : 0 ≤ a ∧ a < (2^64 : Int) := by norm_num; omega
                have brange : 0 ≤ b ∧ b < (2^64 : Int) := by norm_num; omega
                let l : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore a.toNat (by norm_num; omega)
                let r : Aeneas.Std.U64 := Aeneas.Std.U64.ofNatCore b.toNat (by norm_num; omega)
                have lv : (l.val : Int) = a := by simp only [l, Aeneas.Std.U64.ofNatCore, Aeneas.Std.UScalar.ofNatCore_val_eq, Int.toNat_of_nonneg arange.1]
                have rv : (r.val : Int) = b := by simp only [r, Aeneas.Std.U64.ofNatCore, Aeneas.Std.UScalar.ofNatCore_val_eq, Int.toNat_of_nonneg brange.1]
                have dl : Lynx.Rustler.decodeUnsigned .U64 64 (.integer a) = .ok l := by
                  have h : Lynx.Rustler.encodeUnsigned l = .integer a := by simp [Lynx.Rustler.encodeUnsigned, lv]
                  rw [← h]
                  exact Lynx.Rustler.decodeUnsigned_encodeUnsigned l
                have dr : Lynx.Rustler.decodeUnsigned .U64 64 (.integer b) = .ok r := by
                  have h : Lynx.Rustler.encodeUnsigned r = .integer b := by simp [Lynx.Rustler.encodeUnsigned, rv]
                  rw [← h]
                  exact Lynx.Rustler.decodeUnsigned_encodeUnsigned r
                by_cases ordered : a ≤ b
                · have rust_ordered : l ≤ r := by change l.val ≤ r.val; omega
                  simp [«orders_fields:ensures/2», Elixir.__NATIVE__.«derived_pair/2»,
                    Elixir.__NATIVE__.«derived_pair:execution/2», dl, dr,
                    RustWorkspace.DerivedTuple.facade_spec, RustWorkspace.DerivedTuple.encoder_spec,
                    rust_ordered, lv, rv, ordered, Int.isLE_compare, Erlang.erlang.«==/2»]
                · have rust_ordered : ¬ l ≤ r := by change ¬ l.val ≤ r.val; omega
                  simp [«orders_fields:ensures/2», Elixir.__NATIVE__.«derived_pair/2»,
                    Elixir.__NATIVE__.«derived_pair:execution/2», dl, dr,
                    RustWorkspace.DerivedTuple.facade_spec, RustWorkspace.DerivedTuple.encoder_spec,
                    rust_ordered, lv, rv, ordered, Int.isLE_compare, Erlang.erlang.«==/2»]
                """
            end
            ''',
            ["__NATIVE__", "__LAW__"],
            fn
              "__NATIVE__" -> native_module
              "__LAW__" -> "LynxDerived#{suffix}.Laws"
            end
          )
        )

      export = Path.join(tmp, "derived.export")
      law_options = [native: {Lynx.Rustler, options}, export: export]
      reports = Lynx.Laws.verify([beam], law_options)

      assert Enum.all?(reports, &(&1.status == :ok)),
             inspect(
               for report <- reports,
                   report.status != :ok,
                   do: Map.take(report, [:module, :diagnostics])
             )

      assert Enum.all?(
               Lynx.Laws.verify([beam], Keyword.delete(law_options, :export)),
               &(&1.status == :ok and &1.cached)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      original = File.read!(property)

      for extra <- [
            "private axiom derivedTrust : False",
            "private theorem unfinishedDerived : True := by sorry"
          ] do
        File.write!(property, original <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      File.write!(property, original)

      swapped =
        String.replace(
          original_native,
          "    low: u64,\n    high: u64,",
          "    high: u64,\n    low: u64,"
        )

      refute swapped == original_native
      File.write!(native, swapped)
      assert_raise RuntimeError, ~r/DerivedTuple.lean:/, fn -> Lynx.Rustler.prepare!(options) end
      File.write!(native, original_native)
      core = Path.join(workspace, "core/src/lib.rs")
      original_core = File.read!(core)
      [prefix, body] = String.split(original_core, "pub fn order_pair", parts: 2)

      changed =
        prefix <>
          "pub fn order_pair" <>
          String.replace(body, "left <= right", "left >= right", global: false)

      refute changed == original_core
      File.write!(core, changed)
      assert_raise RuntimeError, ~r/DerivedTuple.lean:/, fn -> Lynx.Rustler.prepare!(options) end
      File.write!(core, original_core)
      assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
    end
  end
end
