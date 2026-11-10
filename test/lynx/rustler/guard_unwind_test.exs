defmodule Lynx.Rustler.GuardUnwindTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RUNTIME_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_CAPTURED_RUNTIME_DIR for guard unwind NIF proofs")

  @tag :tmp_dir
  test "compiled Rustler guard cleanup composes into Elixir laws", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxGuardUnwindFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Guard"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))

    options = [
      workspace: workspace,
      package: "ownership-nif",
      tools: @tools,
      root_attribute: "lynx::guard_unwind",
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["guard-unwind"]],
      only: [guarded_value: 2],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Guard.Extraction"
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{"name" => "guarded_value", "arity" => 2, "flags" => 1, "captured_unwind" => true} =
               binding
           ] = prepared.bindings.bindings

    assert Enum.all?(prepared.external.purities, fn {_, purity} -> purity == :concurrent end)

    properties =
      File.read!(Path.join(@fixture, "GuardNifProperties.lean"))
      |> String.replace("__GUARDED__", binding["lean_name"])

    File.write!(Path.join(project, "Guard/Properties.lean"), properties)

    options =
      options ++
        [
          proof_modules: ["Guard.Properties"],
          required_properties:
            ~w(Guard.Properties.mutate Guard.Properties.run_composes Guard.Properties.run_heap Guard.Properties.local_scope Guard.Properties.adapter_continuation Guard.Properties.handler_prefix)
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))
    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
    stub = Path.join(workspace, "elixir/native.ex")

    File.write!(
      stub,
      File.read!(stub)
      |> String.replace("LynxOwnershipFixture", "LynxGuardUnwindFixture")
      |> String.replace(
        "\nend\n",
        "\n  def guarded_value(_value, _accepted), do: :erlang.nif_error(:not_loaded)\nend\n"
      )
    )

    Code.compile_file(stub)
    native = LynxGuardUnwindFixture.Native
    assert apply(native, :guarded_value, [true, true]) == true
    assert apply(native, :guarded_value, [false, true]) == true
    assert catch_error(apply(native, :guarded_value, [true, false])) == :nif_panicked
    assert_raise ArgumentError, fn -> apply(native, :guarded_value, [7, true]) end
    assert_raise ArgumentError, fn -> apply(native, :guarded_value, [true, 7]) end
    laws = Path.join(workspace, "elixir/guard_laws.ex")
    [{_, beam}] = Code.compile_file(laws)
    export = Path.join(tmp, "guard-nif.export")

    law_options = [
      native: {Lynx.Rustler, options},
      export: export,
      initial_environment: "Guard.Properties.initial"
    ]

    reports = Lynx.Laws.verify([beam], law_options)

    errors =
      for report <- reports,
          report.status != :ok,
          do: %{module: report.module, diagnostics: report.diagnostics}

    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 5

    assert Enum.all?(
             Lynx.Laws.verify([beam], Keyword.delete(law_options, :export)),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
