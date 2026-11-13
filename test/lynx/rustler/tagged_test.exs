defmodule Lynx.Rustler.TaggedTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do:
      @moduletag(
        skip: "set LYNX_UNPATCHED_AENEAS_DIR or LYNX_AENEAS_DIR for tagged Encoder proofs"
      )

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "proves the actual derived tagged Encoder with Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = String.replace(version, ".", "")
      native_module = "LynxTagged#{suffix}.Native"
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
            String.replace(source, "fn tagged_order(", "#[verify::start_from]\nfn tagged_order(")
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
      File.mkdir_p!(Path.join(project, "Tagged"))
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
        cargo: [features: ["derived-tagged"]],
        only: [tagged_reply: 2],
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "Tagged.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)

      assert [
               %{
                 "name" => "tagged_reply",
                 "rust_name" => "tagged_order",
                 "flags" => 1,
                 "result" => %{"encoder_definition_id" => encoder_id}
               } = binding
             ] = prepared.bindings.bindings

      validate_metadata(prepared, options)

      property = Path.join(project, "Tagged/Properties.lean")

      properties =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/Tagged.lean"))
        |> String.replace("__TAGGED_IMPLEMENTATION__", binding["lean_name"])

      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["Tagged.Properties"],
            required_properties:
              Enum.map(
                ~w(core_spec caller_spec facade_spec encoder_spec encoded_facade),
                &("Tagged.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)

      assert Enum.any?(prepared.verification.guarantees, fn proof ->
               proof.kind == :cross_crate_contract and
                 proof.theorem == "Tagged.Properties.caller_spec" and
                 "Tagged.Properties.core_spec" in proof.contracts_used
             end)

      assert Enum.any?(prepared.verification.guarantees, fn proof ->
               proof.kind == :rust_implementation and
                 proof.theorem == "Tagged.Properties.encoder_spec" and
                 String.ends_with?(proof.file, "nif/src/lib.rs")
             end)

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "atom cache FFI")
             )

      missing = %{
        prepared.extraction.audit
        | functions:
            Enum.reject(prepared.extraction.audit.functions, &(&1["def_id"] == encoder_id))
      }

      assert_raise ArgumentError, ~r/missing, opaque or mismatched.*Encoder/, fn ->
        Lynx.Rustler.Bindings.link!(prepared.bindings, missing, prepared.extraction.translation)
      end

      library = Path.join(tmp, "tagged_native")
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

      for {left, right, expected} <- [
            {0, 0, :empty},
            {7, 7, {:equal, 7}},
            {9, 4, {:ordered, 4, 9}},
            {4, 9, {:ordered, 4, 9}},
            {0, 18_446_744_073_709_551_615, {:ordered, 0, 18_446_744_073_709_551_615}}
          ],
          do: assert(apply(native_atom, :tagged_reply, [left, right]) == expected)

      for args <- [[-1, 0], [0, 18_446_744_073_709_551_616], [true, 0]],
          do: assert_raise(ArgumentError, fn -> apply(native_atom, :tagged_reply, args) end)

      [{_, beam}] = Code.compile_string(laws(native_module, suffix))
      export = Path.join(tmp, "tagged.export")
      reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

      for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
          do:
            assert(
              Enum.any?(Enum.flat_map(reports, &Map.get(&1, :guarantees, [])), &(&1.kind == kind))
            )

      # A fresh proc-macro expansion can change the generated cache record's
      # layout. Its changed Lean definitions must not reuse an older proof.
      # Reusing the identical verified artifact has a deterministic cache key.
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
            "private axiom taggedTrust : False",
            "private theorem unfinishedTag : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      wrong =
        String.replace(
          properties,
          ".integer left.val, .integer right.val",
          ".integer right.val, .integer left.val"
        )

      refute wrong == properties
      File.write!(property, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(property, properties)

      File.write!(
        native,
        String.replace(
          source,
          "OrderedReply::Ordered(low, high)",
          "OrderedReply::Ordered(high, low)"
        )
      )

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(native, source)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end

  defp validate_metadata(prepared, options) do
    audit = prepared.extraction.audit

    {id, _} =
      Enum.find(audit.external_calls, fn {_, model} ->
        model.lean == "Lynx.Rustler.Encoding.triple"
      end)

    function = Enum.find(audit.translated["fun_decls"], &(&1 && &1["def_id"] == id))

    assert %{encoder_slots: 3} =
             Lynx.Rustler.EncoderModels.resolve(function, audit.translated, audit.references)

    for changed <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["generics", "trait_clauses"], []),
          put_in(function, ["generics", "outlives"], []),
          update_in(function, ["signature", "inputs"], &Enum.reverse/1)
        ] do
      assert Lynx.Rustler.EncoderModels.resolve(changed, audit.translated, audit.references) ==
               nil
    end

    roots = [
      "experiment_nif::_::__INVENTORY::nif_func::wrapper::_::tagged_order"
      | Lynx.Rustler.Bindings.encoder_roots(prepared.bindings)
    ]

    raw =
      Lynx.Rust.Extraction.describe!(
        prepared.context,
        @tools,
        roots,
        prepared.project,
        "Tagged.CacheCheck",
        external_types: audit.external_types,
        root_attribute: options[:root_attribute]
      )

    caches =
      Lynx.Rustler.Metadata.atom_caches!(
        prepared.expanded,
        Lynx.Rustler.AtomCaches.modules(raw.document)
      )

    [cache] = caches
    expected = Lynx.Rustler.AtomCaches.resolve!(raw.document, caches)

    assert Lynx.Rustler.AtomCaches.resolve!(raw.document, [
             %{cache | "fields" => Enum.reverse(cache["fields"])}
           ]) == expected

    for fields <- [
          tl(cache["fields"]),
          cache["fields"] ++ cache["fields"],
          [Map.put(hd(cache["fields"]), "atom", "incorrect_tag") | tl(cache["fields"])]
        ] do
      assert_raise ArgumentError, ~r/compiled Rustler atom/, fn ->
        Lynx.Rustler.AtomCaches.resolve!(raw.document, [%{cache | "fields" => fields}])
      end
    end

    drop =
      Enum.find(raw.document["translated"]["fun_decls"], fn
        %{
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["result", 0]},
              %{"Ident" => ["Result", 0]},
              %{"Impl" => _},
              %{"Builtin" => ["DropGlue", 0]}
            ]
          }
        } ->
          true

        _ ->
          false
      end)

    changed =
      if drop do
        poison_drop(raw.document, drop["def_id"])
      else
        # Some compiler profiles omit the intermediate Result cleanup. Retain
        # the drop-type mutation when captured, and otherwise corrupt an actual
        # initializer call instead of requiring nonexistent metadata.
        update_in(raw.document, ["translated", "fun_decls"], fn functions ->
          Enum.map(functions, fn
            %{"item_meta" => %{"name" => name}} = function ->
              if List.last(name) == %{"Ident" => ["expect", 0]} do
                put_in(
                  function,
                  ["item_meta", "name"],
                  Enum.drop(name, -1) ++ [%{"Ident" => ["unsupported_call", 0]}]
                )
              else
                function
              end

            function ->
              function
          end)
        end)
      end

    refute changed == raw.document

    assert_raise ArgumentError, ~r/compiled Rustler atom cache/, fn ->
      Lynx.Rustler.AtomCaches.resolve!(changed, caches)
    end
  end

  defp poison_drop(%{"kind" => %{"Fun" => id}, "generics" => args} = value, id),
    do: %{value | "generics" => %{args | "types" => [%{"Scalar" => "Bool"} | tl(args["types"])]}}

  defp poison_drop(map, id) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, poison_drop(value, id)} end)

  defp poison_drop(list, id) when is_list(list), do: Enum.map(list, &poison_drop(&1, id))
  defp poison_drop(value, _), do: value

  defp laws(native, suffix) do
    """
    defmodule LynxTagged#{suffix}.Laws do
      @compile :debug_info
      use Lynx.Laws
      law equal_fields(value),
        requires: is_integer(value) and value >= 0 and value <= 18_446_744_073_709_551_615,
        expects: #{native}.tagged_reply(value, value) == if(value == 0, do: :empty, else: {:equal, value}),
        proof: ~LEAN\"\"\"
        cases value <;> simp [«equal_fields:requires/1», Erlang.erlang.«is_integer/1»] at requires
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
        by_cases az : a = 0 <;>
          simp_all [«equal_fields:ensures/1», Elixir.#{native}.«tagged_reply/2»,
            Elixir.#{native}.«tagged_reply:execution/2», decoded,
            Tagged.Properties.facade_spec, Tagged.Properties.encoder_spec,
            Tagged.Properties.replyTerm, Tagged.Properties.response, zero, az, vv,
            Erlang.erlang.«==/2»]
        \"\"\"
      law ordered_fields,
        expects: #{native}.tagged_reply(9, 4) == {:ordered, 4, 9},
        proof: ~LEAN\"\"\"
        have dl : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 9) = .ok 9#u64 := by
          have encoded : Lynx.Rustler.encodeUnsigned (9#u64) = .integer 9 := by simp [Lynx.Rustler.encodeUnsigned]
          rw [← encoded]
          exact Lynx.Rustler.decodeUnsigned_encodeUnsigned 9#u64
        have dr : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 4) = .ok 4#u64 := by
          have encoded : Lynx.Rustler.encodeUnsigned (4#u64) = .integer 4 := by simp [Lynx.Rustler.encodeUnsigned]
          rw [← encoded]
          exact Lynx.Rustler.decodeUnsigned_encodeUnsigned 4#u64
        simp [«ordered_fields:ensures/0», Elixir.#{native}.«tagged_reply/2»,
          Elixir.#{native}.«tagged_reply:execution/2», dl, dr,
          Tagged.Properties.facade_spec, Tagged.Properties.encoder_spec,
          Tagged.Properties.replyTerm, Tagged.Properties.response,
          Aeneas.Std.UScalar.le_equiv, Erlang.erlang.«==/2»]
        \"\"\"
    end
    """
  end
end
