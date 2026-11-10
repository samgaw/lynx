defmodule Lynx.Rustler.ResourceReturnTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_RESOURCE_RETURN_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_RESOURCE_RETURN_DIR for owned resource return NIF laws")

  @tag :tmp_dir
  test "ordinary laws pass returned resource terms between compiled NIFs", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxResourceReturnFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Returned"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))

    options = [
      workspace: workspace,
      package: "ownership-nif",
      tools: @tools,
      root_attribute: "lynx::resource_return",
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["resource-return"]],
      only: [resource_allocate: 2, resource_checked: 2],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Returned.Extraction"
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert length(prepared.bindings.bindings) == 2
    allocated = Enum.find(prepared.bindings.bindings, &(&1["name"] == "resource_allocate"))
    checked = Enum.find(prepared.bindings.bindings, &(&1["name"] == "resource_checked"))
    assert %{"arity" => 2, "flags" => 1, "captured_unwind" => true} = allocated
    assert %{"arity" => 2, "flags" => 1, "captured_unwind" => true} = checked

    assert %{
             status: :validated_configuration,
             types: [%{rust_name: "ownership_nif::UnwindResource"}]
           } = prepared.resource_registration

    File.cp!(
      Path.join(@fixture, "ResourceReturnProperties.lean"),
      Path.join(project, "Returned/Properties.lean")
    )

    File.cp!(
      Path.join(@fixture, "ResourceFrameProperties.lean"),
      Path.join(project, "Returned/Framed.lean")
    )

    properties =
      File.read!(Path.join(@fixture, "ResourceReturnNifProperties.lean"))
      |> String.replace("__ALLOCATE__", allocated["lean_name"])
      |> String.replace("__CHECKED__", checked["lean_name"])

    File.write!(Path.join(project, "Returned/NifProperties.lean"), properties)

    required =
      ~w(mutate checked allocate allocate_registered allocate_unregistered encoded_return encoded_next decoded_return adapter_roundtrip)

    options =
      options ++
        [
          proof_modules: ["Returned.Properties", "Returned.Framed", "Returned.NifProperties"],
          required_properties:
            Enum.map(required, &("Returned.Properties." <> &1)) ++
              Enum.map(
                ~w(allocate_next allocate_twice rejected_after_return),
                &("Returned.Framed." <> &1)
              )
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
      |> String.replace("LynxOwnershipFixture", "LynxResourceReturnFixture")
      |> String.replace(
        "\nend\n",
        "\n  def resource_checked(_resource, _accepted), do: :erlang.nif_error(:not_loaded)\n  def resource_seed(_value), do: :erlang.nif_error(:not_loaded)\n  def resource_created(_value, _accepted), do: :erlang.nif_error(:not_loaded)\n  def resource_allocate(_value, _accepted), do: :erlang.nif_error(:not_loaded)\nend\n"
      )
    )

    Code.compile_file(stub)
    native = LynxResourceReturnFixture.Native

    for value <- [false, true] do
      resource = apply(native, :resource_allocate, [value, true])
      assert apply(native, :resource_checked, [resource, true]) == value
      assert apply(native, :resource_checked, [resource, true]) == value
      assert catch_error(apply(native, :resource_allocate, [value, false])) == :nif_panicked
    end

    first = apply(native, :resource_allocate, [true, true])
    second = apply(native, :resource_allocate, [false, true])
    assert apply(native, :resource_checked, [first, true])
    refute apply(native, :resource_checked, [second, true])
    assert catch_error(apply(native, :resource_allocate, [false, false])) == :nif_panicked
    assert apply(native, :resource_checked, [first, true])
    refute apply(native, :resource_checked, [second, true])

    for args <- [[7, true], [true, 7]],
        do: assert_raise(ArgumentError, fn -> apply(native, :resource_allocate, args) end)

    [{law_module, beam}] =
      Code.compile_file(Path.join(workspace, "elixir/resource_return_laws.ex"))

    for law <-
          ~w(returns_true returns_false rejects_after_creation rejects_first_argument rejects_second_argument rejects_later_decoding retains_handle independent_handles preserves_prior_handle)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "resource-return.export")
    opts = [native: {Lynx.Rustler, options}]
    reports = Lynx.Laws.verify([beam], opts ++ [export: export])
    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 9
    assert Enum.all?(Lynx.Laws.verify([beam], opts), &(&1.status == :ok and &1.cached))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
