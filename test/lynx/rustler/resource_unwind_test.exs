defmodule Lynx.Rustler.ResourceUnwindTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RESOURCE_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RESOURCE_DIR for resource unwind NIF proofs")

  @tag :tmp_dir
  test "compiled resource calls retain the VM pin after success, panic and badarg", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxResourceUnwindFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Resource"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))

    options = [
      workspace: workspace,
      package: "ownership-nif",
      tools: @tools,
      root_attribute: "lynx::resource_unwind",
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["resource-unwind"]],
      only: [resource_checked: 2],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Resource.Extraction"
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "resource_checked",
               "arity" => 2,
               "flags" => 1,
               "captured_unwind" => true
             } = binding
           ] = prepared.bindings.bindings

    assert %{
             status: :validated_configuration,
             types: [%{rust_name: "ownership_nif::UnwindResource"}]
           } = prepared.resource_registration

    registration = prepared.resource_registration
    raw = registration.compiler_file |> File.read!() |> JSON.decode!()
    [entry] = registration.metadata["registrations"]
    parent = [%{"Ident" => ["ownership_nif", 0]}, %{"Ident" => ["_", entry["anonymous_index"]]}]
    table_name = parent ++ [%{"Ident" => ["__CTOR", 0]}]

    missing =
      update_in(raw, ["translated", "global_decls"], fn globals ->
        Enum.reject(globals, &(&1 && &1["item_meta"]["name"] == table_name))
      end)

    assert_raise ArgumentError, ~r/missing or inconsistent compiler resource registration/, fn ->
      Lynx.Rustler.Registrations.resolve!(registration.metadata, missing, "ownership_nif")
    end

    [table] =
      Enum.filter(
        raw["translated"]["global_decls"],
        &(&1 && &1["item_meta"]["name"] == table_name)
      )

    table_id = table["def_id"]

    changed =
      update_in(raw, ["translated", "fun_decls"], fn functions ->
        Enum.map(functions, fn function ->
          case function do
            %{"src" => %{"GlobalInitializer" => %{"id" => ^table_id}}} ->
              Map.put(function, "body", "Opaque")

            _ ->
              function
          end
        end)
      end)

    assert_raise ArgumentError, ~r/missing resource initializer implementation/, fn ->
      Lynx.Rustler.Registrations.resolve!(registration.metadata, changed, "ownership_nif")
    end

    ctor_name = parent ++ [%{"Ident" => ["__ctor", 0]}]
    functions = raw["translated"]["fun_decls"]
    [ctor] = Enum.filter(functions, &(&1 && &1["item_meta"]["name"] == ctor_name))

    wrong_pointer =
      put_in(
        raw,
        ["translated", "fun_decls"],
        Enum.map(functions, fn function ->
          if function == ctor,
            do:
              put_in(function, ["item_meta", "name"], parent ++ [%{"Ident" => ["other_ctor", 0]}]),
            else: function
        end) ++ [Map.put(ctor, "def_id", length(functions))]
      )

    assert_raise ArgumentError,
                 ~r/constructor table does not retain its actual constructor/,
                 fn ->
                   Lynx.Rustler.Registrations.resolve!(
                     registration.metadata,
                     wrong_pointer,
                     "ownership_nif"
                   )
                 end

    properties =
      File.read!(Path.join(@fixture, "ResourceUnwindProperties.lean"))
      |> String.replace("__RESOURCE__", binding["lean_name"])

    File.write!(Path.join(project, "Resource/Properties.lean"), properties)

    options =
      options ++
        [
          proof_modules: ["Resource.Properties"],
          required_properties:
            ~w(Resource.Properties.mutate Resource.Properties.checked Resource.Properties.inner Resource.Properties.facade Resource.Properties.inner_final Resource.Properties.facade_final Resource.Properties.adapter_continuation Resource.Properties.handler_prefix)
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.any?(
             prepared.verification.unverified_nif_exports,
             &(&1.function == "resource_seed" and &1.status == :unverified)
           )

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
    stub = Path.join(workspace, "elixir/native.ex")

    File.write!(
      stub,
      File.read!(stub)
      |> String.replace("LynxOwnershipFixture", "LynxResourceUnwindFixture")
      |> String.replace(
        "\nend\n",
        "\n  def resource_checked(_resource, _accepted), do: :erlang.nif_error(:not_loaded)\n  def resource_seed(_value), do: :erlang.nif_error(:not_loaded)\n  def resource_created(_value, _accepted), do: :erlang.nif_error(:not_loaded)\nend\n"
      )
    )

    Code.compile_file(stub)
    native = LynxResourceUnwindFixture.Native
    handle = apply(native, :resource_seed, [true])
    assert apply(native, :resource_checked, [handle, true]) == false
    assert catch_error(apply(native, :resource_checked, [handle, false])) == :nif_panicked
    assert apply(native, :resource_checked, [handle, true]) == false

    for args <- [[7, true], [handle, 7]],
        do: assert_raise(ArgumentError, fn -> apply(native, :resource_checked, args) end)

    laws = Path.join(workspace, "elixir/resource_unwind_laws.ex")
    [{law_module, beam}] = Code.compile_file(laws)
    previous = Process.put(:held, handle)

    try do
      for law <-
            ~w(reads_resource repeated_calls panic_releases_owners rejects_wrong_resource rejects_later_argument)a,
          do: assert(apply(law_module, law, []))
    after
      if previous, do: Process.put(:held, previous), else: Process.delete(:held)
    end

    export = Path.join(tmp, "resource-unwind.export")
    opts = [native: {Lynx.Rustler, options}, initial_environment: "Resource.Properties.initial"]
    reports = Lynx.Laws.verify([beam], opts ++ [export: export])

    errors =
      for report <- reports,
          report.status != :ok,
          do: %{module: report.module, diagnostics: report.diagnostics}

    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 5
    assert Enum.all?(Lynx.Laws.verify([beam], opts), &(&1.status == :ok and &1.cached))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    [{_, unselected}] =
      Code.compile_string("""
      defmodule LynxResourceUnwindFixture.Unselected do
        @compile :debug_info
        use Lynx.Laws
        law constructor, expects: is_reference(LynxResourceUnwindFixture.Native.resource_seed(true)),
          proof: ~LEAN"by simp"
      end
      """)

    assert_raise CompileError, ~r/unregistered external implementation.*resource_seed/, fn ->
      Lynx.Laws.verify([unselected], externals: [prepared.external], lean_project: project)
    end
  end
end
