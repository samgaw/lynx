defmodule Lynx.Rustler.ResourceCreationTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RESOURCE_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RESOURCE_DIR for resource creation NIF laws")

  @tag :tmp_dir
  test "ordinary laws create and consume resources without a supplied handle", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxResourceCreationFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Created"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))

    options = [
      workspace: workspace,
      package: "ownership-nif",
      tools: @tools,
      root_attribute: "lynx::resource_create",
      proof_roots: ["ownership_nif::create_with_mutex"],
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["resource-unwind"]],
      only: [resource_created: 2],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Created.Extraction"
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "resource_created",
               "arity" => 2,
               "flags" => 1,
               "captured_unwind" => true
             } = binding
           ] = prepared.bindings.bindings

    assert %{
             status: :validated_configuration,
             types: [%{rust_name: "ownership_nif::UnwindResource"}]
           } = prepared.resource_registration

    File.cp!(
      Path.join(@fixture, "ResourceCreateProperties.lean"),
      Path.join(project, "Created/Properties.lean")
    )

    properties =
      File.read!(Path.join(@fixture, "ResourceCreateNifProperties.lean"))
      |> String.replace("__CREATED__", binding["lean_name"])

    File.write!(Path.join(project, "Created/NifProperties.lean"), properties)

    required =
      ~w(mutate checked inner create create_registered create_unregistered cleanup_registered cleanup_unregistered facade adapter_continuation adapter_handled)

    options =
      options ++
        [
          proof_modules: ["Created.Properties", "Created.NifProperties"],
          required_properties: Enum.map(required, &("Created.Properties." <> &1))
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.any?(
             prepared.verification.unverified_nif_exports,
             &(&1.function == "resource_seed")
           )

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
    stub = Path.join(workspace, "elixir/native.ex")

    File.write!(
      stub,
      File.read!(stub)
      |> String.replace("LynxOwnershipFixture", "LynxResourceCreationFixture")
      |> String.replace(
        "\nend\n",
        "\n  def resource_checked(_resource, _accepted), do: :erlang.nif_error(:not_loaded)\n  def resource_seed(_value), do: :erlang.nif_error(:not_loaded)\n  def resource_created(_value, _accepted), do: :erlang.nif_error(:not_loaded)\nend\n"
      )
    )

    Code.compile_file(stub)
    native = LynxResourceCreationFixture.Native

    for value <- [false, true] do
      assert apply(native, :resource_created, [value, true]) == not value
      assert catch_error(apply(native, :resource_created, [value, false])) == :nif_panicked
      assert apply(native, :resource_created, [value, true]) == not value
    end

    for args <- [[7, true], [true, 7]],
        do: assert_raise(ArgumentError, fn -> apply(native, :resource_created, args) end)

    [{law_module, beam}] =
      Code.compile_file(Path.join(workspace, "elixir/resource_create_laws.ex"))

    for law <-
          ~w(creates_true creates_false rejects_after_creation rejects_first_argument rejects_second_argument repeated_creation)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "resource-creation.export")
    opts = [native: {Lynx.Rustler, options}]
    reports = Lynx.Laws.verify([beam], opts ++ [export: export])
    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 6
    assert Enum.all?(Lynx.Laws.verify([beam], opts), &(&1.status == :ok and &1.cached))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
