defmodule Lynx.Rustler.TupleVecTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR") || System.get_env("LYNX_PURE_AENEAS_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do:
      @moduletag(
        skip: "set LYNX_UNPATCHED_AENEAS_DIR or LYNX_PURE_AENEAS_DIR for tuple-vector proofs"
      )

  for version <- ~w(0.39.0 0.38.0) do
    @tag :tmp_dir
    @tag rustler: version
    test "verifies byte-bounded tuple-vector inputs through Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      prefix = "TupleVec" <> String.replace(version, ".", "")
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for name <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

      source = Path.join(workspace, "nif/src/lib.rs")

      File.write!(
        source,
        "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
          (File.read!(source)
           |> String.replace("LynxRustFixture.Native", prefix <> ".Native")
           |> String.replace(
             ~r/fn (replace_first_pair|replace_alias_records|replace_alias_batch)\(/,
             "#[verify::start_from]\nfn \\1("
           ))
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
      File.mkdir_p!(Path.join(project, prefix))
      File.mkdir_p!(Path.join(project, ".lake"))

      File.ln_s!(
        Path.join(@fixture, "proofs/.lake/packages"),
        Path.join(project, ".lake/packages")
      )

      base = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        root_attribute: "verify::start_from",
        cargo: [features: ["tuple-vec"]],
        only: [update_records: 2, alias_records: 2, alias_batch: 2],
        lean_project: project,
        module_prefix: prefix <> ".Extraction",
        build_dir: Path.join(tmp, "build")
      ]

      discovered = Lynx.Rustler.prepare!(base)

      assert length(discovered.bindings.bindings) == 3

      for binding <- discovered.bindings.bindings do
        assert %{
                 "arity" => 2,
                 "arguments" => [%{"vec" => %{"tuple" => ["i64", "u64"]}}, "i64"],
                 "result" => %{"tuple" => ["bool", %{"vec" => %{"tuple" => ["i64", "u64"]}}]},
                 "tuple_input_bounds" => [
                   %{"bytes" => 16, "maximum" => 9_223_372_036_854_775_807}
                 ]
               } = binding

        assert binding["flags"] == if(binding["name"] == "update_records", do: 1, else: 0)
      end

      facade =
        Enum.find(discovered.bindings.bindings, &(&1["name"] == "update_records"))["lean_name"]

      assert [%{bytes: 16}] = discovered.extraction.tuple_layouts.queries

      assert %{"aeneas_version" => "build-2b9e3ea", "charon_version" => "0.1.304"} =
               discovered.extraction.translation

      property = Path.join(project, prefix <> "/Properties.lean")

      proof =
        File.read!(Path.join(@proofs, "TupleVector.lean"))
        |> String.replace("__PREFIX__", prefix)
        |> String.replace("__CORE__", "experiment_nif.experiment_core.collections")
        |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")
        |> String.replace("__FACADE__", facade)

      File.write!(property, proof)

      aliases = Enum.reject(discovered.bindings.bindings, &(&1["name"] == "update_records"))

      alias_proofs =
        for binding <- aliases do
          name = binding["lean_name"]

          """
          theorem #{binding["name"]}_spec (input : alloc.vec.Vec (I64 × U64)) (value : I64) :
              #{name} input value = RustM.ok (!input.val.isEmpty, #{prefix}.Properties.updatedVector input value) := by
            simpa [#{name}] using #{prefix}.Properties.composition input value
          """
        end

      File.write!(Path.join(project, prefix <> "/AliasProperties.lean"), """
      module
      public import #{prefix}.Properties
      public section
      open Aeneas Aeneas.Std
      namespace #{prefix}.AliasProperties
      #{Enum.join(alias_proofs, "\n")}
      end #{prefix}.AliasProperties
      """)

      options =
        base ++
          [
            proof_modules: [prefix <> ".Properties", prefix <> ".AliasProperties"],
            required_properties:
              Enum.map(
                ~w(slice_transition vector_transition composition preserves_fields facade_spec),
                &(prefix <> ".Properties." <> &1)
              ) ++ Enum.map(aliases, &(prefix <> ".AliasProperties." <> &1["name"] <> "_spec"))
          ]

      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.all?(prepared.reports, &(&1.status == :ok))

      assert Enum.any?(prepared.verification.guarantees, fn evidence ->
               evidence.kind == :cross_crate_contract and
                 evidence.theorem == prefix <> ".Properties.composition" and
                 (prefix <> ".Properties.vector_transition") in evidence.contracts_used
             end)

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "closed scalar tuples")
             )

      adapter_evidence = Enum.filter(prepared.verification.guarantees, &(&1.kind == :nif_adapter))
      assert length(adapter_evidence) == 3

      assert Enum.all?(
               adapter_evidence,
               &match?(
                 %{
                   tuple_input_bounds: [%{"bytes" => 16, "maximum" => 9_223_372_036_854_775_807}]
                 },
                 &1
               )
             )

      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

      invalid =
        put_in(
          prepared.bindings,
          [:bindings, Access.at(0), "tuple_input_bounds", Access.at(0), "maximum"],
          0
        )

      external =
        Lynx.Rustler.Adapter.external!(invalid, prepared.extraction.implementations,
          bridge_module: prefix <> ".RustlerBridge",
          implementation_module: prefix <> ".RejectedByteBound",
          proof_modules: [prefix <> ".Properties"]
        )

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, external.files)

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unsolved goals"))

      error =
        assert_raise CompileError, ~r/tuple vector argument requires/, fn ->
          Lynx.Rustler.Bindings.link!(
            prepared.bindings,
            prepared.extraction.audit,
            prepared.extraction.translation
          )
        end

      assert error.file =~ "nif/src/lib.rs"
      assert is_integer(error.line)

      mismatch =
        put_in(prepared.bindings, [:bindings, Access.at(0), "arguments", Access.at(0)], %{
          "vec" => %{"tuple" => ["u64", %{"native" => ["RecordTag"]}]}
        })

      assert_raise ArgumentError, ~r/compiled vector element types differ/, fn ->
        Lynx.Rustler.Bindings.resolve!(
          mismatch,
          %{"translated" => prepared.extraction.audit.translated},
          prepared.extraction.audit.first_party
        )
      end

      library = Path.join(tmp, "native")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {name, arity, _} <- prepared.bindings.exports,
            do:
              "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      Code.compile_string("""
      defmodule #{prefix}.Native do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}",0)
        #{Enum.join(stubs, "\n")}
      end
      """)

      compiled_laws =
        for binding <- discovered.bindings.bindings do
          [{module, beam}] =
            File.read!(Path.join(@proofs, "tuple_vector_laws.ex"))
            |> String.replace("__MODULE__", prefix)
            |> String.replace(
              "defmodule #{prefix}.Laws do",
              "defmodule #{prefix}.#{Macro.camelize(binding["name"])}Laws do"
            )
            |> String.replace("update_records", binding["name"])
            |> Code.compile_string()

          for law <-
                ~w(update empty signed_bounds wrong_arity unsigned_range signed_range non_list invalid_head_before_improper_tail improper_tail_panics first_argument_panics_before_second_argument)a,
              do: assert(apply(module, law, []))

          beam
        end

      export = Path.join(tmp, "tuple.export")
      law_options = [native: {Lynx.Rustler, options}]
      reports = Lynx.Laws.verify(compiled_laws, Keyword.put(law_options, :export, export))
      assert [] == for(r <- reports, r.status != :ok, do: {r.module, r.diagnostics})
      assert length(Enum.flat_map(reports, & &1.theorems)) == 30

      assert Enum.all?(
               Lynx.Laws.verify(compiled_laws, law_options),
               &(&1.status == :ok and &1.cached)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      for extra <- [
            "private axiom tupleTrust : False",
            "private theorem unfinishedTuple : True := by sorry"
          ] do
        File.write!(property, proof <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      File.write!(property, proof)

      wrong =
        String.replace(
          proof,
          "experiment_nif.experiment_analysis.replace_first_pair input value =\n      RustM.ok (!input.val.isEmpty, updatedVector input value)",
          "experiment_nif.experiment_analysis.replace_first_pair input value = RustM.ok (false, input)"
        )

      refute wrong == proof
      File.write!(property, wrong)
      assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      File.write!(property, proof)
      core = Path.join(workspace, "core/src/collections.rs")
      original = File.read!(core)
      mutated = String.replace(original, "input[0].0 = value;", "input[0].0 = 0;")
      refute mutated == original
      File.write!(core, mutated)
      assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      File.write!(core, original)

      # A Rustler-derived nominal record is not an alias, even with identical fields.
      File.write!(
        source,
        File.read!(source) <>
          """

          #[derive(rustler::NifTuple)]
          struct NotAlias { signed: i64, unsigned: u64 }
          #[verify::start_from]
          #[rustler::nif]
          fn nominal_records(input: Vec<NotAlias>) -> Vec<NotAlias> { input }
          """
      )

      assert_raise ArgumentError, ~r/unsupported NIF ADT/, fn ->
        Lynx.Rustler.prepare!(Keyword.put(base, :only, nominal_records: 1))
      end

      File.write!(
        source,
        File.read!(source) <>
          """

          #[verify::start_from]
          #[rustler::nif]
          fn string_records(input: Vec<String>) -> Vec<String> { input }
          """
      )

      assert_raise ArgumentError, ~r/unsupported NIF ADT/, fn ->
        Lynx.Rustler.prepare!(Keyword.put(base, :only, string_records: 1))
      end
    end
  end
end
