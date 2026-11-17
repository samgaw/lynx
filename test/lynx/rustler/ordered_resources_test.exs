defmodule Lynx.Rustler.OrderedResourcesTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @tools System.get_env("LYNX_NATIVE_COLLECTIONS_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_NATIVE_COLLECTIONS_DIR for ordered resource NIF proofs")

  @tag :tmp_dir
  test "proves persistent ordered resource calls, concurrent claims and final cleanup", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for name <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@workspace, name), Path.join(workspace, name))

    source = Path.join(workspace, "nif/src/lib.rs")

    rust =
      File.read!(source) |> String.replace("LynxRustFixture.Native", "LynxRegistryFixture.Native")

    rust =
      "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
        Regex.replace(
          ~r/^(fn registry_|pub fn registry_release)/m,
          rust,
          "#[verify::start_from]\n\\1"
        )

    File.write!(source, rust)
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Registry"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.join(@workspace, "proofs/.lake/packages"),
      Path.join(project, ".lake/packages")
    )

    base = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      sysroot: :full_mir,
      root_attribute: "verify::start_from",
      cargo: [features: ["ordered-resources"]],
      only: [registry_new: 0, registry_replace: 3, registry_take: 2, registry_claim: 2],
      lean_project: project,
      module_prefix: "Registry.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(base)

    properties =
      File.read!(Path.join(@proofs, "OrderedRuntime.lean"))
      |> String.replace("__PREFIX__", "Registry")
      |> String.replace("__CORE__", "experiment_nif.experiment_core.ordered")
      |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")

    File.write!(Path.join(project, "Registry/Properties.lean"), properties)

    File.write!(
      Path.join(project, "Registry/ResourceProperties.lean"),
      File.read!(Path.join(@proofs, "OrderedResource.lean"))
      |> String.replace("__PREFIX__", "Registry")
    )

    adapter =
      Enum.reduce(
        [
          {"NEW", "registry_new"},
          {"REPLACE", "registry_replace"},
          {"TAKE", "registry_take"},
          {"CLAIM", "registry_claim"}
        ],
        File.read!(Path.join(@proofs, "OrderedResourceAdapter.lean"))
        |> String.replace("__PREFIX__", "Registry"),
        fn {key, name}, text ->
          binding = Enum.find(discovered.bindings.bindings, &(&1["name"] == name))
          String.replace(text, "__#{key}__", binding["lean_name"])
        end
      )

    nif_properties = Path.join(project, "Registry/NifProperties.lean")
    File.write!(nif_properties, adapter)

    options =
      base ++
        [
          proof_modules:
            ~w(Registry.Properties Registry.ResourceProperties Registry.NifProperties),
          required_properties:
            Enum.map(
              ~w(replace_eq locked_contract replace_run replace_preserves_other take_eq take_contract take_run claim_eq claim_contract claim_run),
              &("Registry.Properties." <> &1)
            ) ++
              Enum.map(
                ~w(cleanup_contract cleanup_run final_release),
                &("Registry.ResourceProperties." <> &1)
              ) ++
              Enum.map(
                ~w(create_contract replace_contract take_contract claim_contract),
                &("Registry.NifProperties." <> &1)
              )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert Enum.any?(
             prepared.verification.resource_cleanup,
             &(&1.lean_name == "experiment_nif.RegistryState.drop_owned")
           )

    assert %{omitted_functions: [_, _], omitted_types: [_, _, _]} =
             prepared.extraction.resource_interface_projection

    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    # Both independently owned fields must remain live until their own consuming calls.
    audit = prepared.extraction.audit
    lifetime!(audit.functions, audit.translated, prepared)

    helper =
      Enum.find(
        audit.functions,
        &(&1["item_meta"]["name"] ==
            Enum.map(~w(experiment_nif RegistryState drop_owned), fn n -> %{"Ident" => [n, 0]} end))
      )

    statements = helper["body"]["Structured"]["body"]["statements"]
    index = Enum.find_index(statements, &match?(%{"kind" => %{"Call" => _}}, &1))

    for changed <- [
          List.delete_at(statements, index),
          List.insert_at(statements, index, Enum.at(statements, index))
        ] do
      bad = put_in(helper, ["body", "Structured", "body", "statements"], changed)

      functions =
        Enum.map(audit.functions, fn f -> if f["def_id"] == bad["def_id"], do: bad, else: f end)

      translated =
        Map.update!(
          audit.translated,
          "fun_decls",
          &Enum.map(&1, fn f -> if f && f["def_id"] == bad["def_id"], do: bad, else: f end)
        )

      assert_raise CompileError, ~r/native owner lifetime/, fn ->
        lifetime!(functions, translated, prepared)
      end
    end

    core = Path.join(workspace, "core/src/ordered.rs")
    original = File.read!(core)

    changed =
      String.replace(
        original,
        "replace_value(&mut guard, key, value)",
        "replace_value(&mut guard, 0, value)"
      )

    refute changed == original
    File.write!(core, changed)
    assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    File.write!(core, original)
    wrong = String.replace(adapter, ".ok previous) := by", ".ok none) := by")
    refute wrong == adapter
    File.write!(nif_properties, wrong)
    assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    File.write!(nif_properties, adapter)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

    file = Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules])
    export = Path.join(tmp, "resource.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    check_export(project, export)
    funs = Path.join(project, "Registry/Extraction/Funs.lean")
    emitted = File.read!(funs)

    missing =
      Regex.replace(
        ~r/instance : Lynx.NativeResourceCleanup experiment_nif\.RegistryState where\n  cleanup :=[^\n]+\n/,
        emitted,
        ""
      )

    refute missing == emitted
    File.write!(funs, missing)

    assert_raise RuntimeError, fn ->
      Lynx.Rust.Project.build!(project, ["Registry.Extraction.Funs"])
    end

    File.write!(funs, emitted)

    for extra <- [
          "private axiom unapproved_resource : False",
          "private theorem unfinished_resource : True := by sorry"
        ] do
      File.write!(nif_properties, adapter <> "\n" <> extra <> "\n")
      assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(nif_properties, adapter)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    Code.compile_string("""
    defmodule LynxRegistryFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    [{module, beam}] = Code.compile_file(Path.join(@proofs, "ordered_resource_laws.ex"))

    for law <-
          ~w(empty updates independent_fields alias_observes rejected_input_preserves invalid_handle concurrent_claims)a,
        do: assert(apply(module, law, []))

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 8192, maxHeartbeats: 24_000_000]
    ]

    law_export = Path.join(tmp, "laws.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, law_export))
    assert [] == for(r <- reports, r.status != :ok, do: {r.module, r.diagnostics})
    assert length(Enum.flat_map(reports, & &1.theorems)) == 7

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do:
          assert(
            Enum.any?(Enum.flat_map(reports, &Map.get(&1, :guarantees, [])), &(&1.kind == kind))
          )

    check_export(project, law_export)
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
  end

  defp lifetime!(functions, translated, prepared) do
    audit = prepared.extraction.audit

    Lynx.Rust.NativeLifetimes.audit!(
      functions,
      audit.external_calls,
      translated,
      audit.references,
      audit.drops,
      [],
      prepared.extraction.allocator_layout
    )
  end

  defp check_export(project, export) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
