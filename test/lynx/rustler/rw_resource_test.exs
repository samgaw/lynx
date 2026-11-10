defmodule Lynx.Rustler.RwResourceTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_RWLOCK_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_RWLOCK_DIR for resource read/write lock proofs")

  @tag :tmp_dir
  test "resource aliases retain shared writes and retire nested cells", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    File.cp_r!(
      Path.expand("../rust_workspace/unrelated", @fixture),
      Path.join(workspace, "unrelated")
    )

    manifest = Path.join(workspace, "Cargo.toml")

    File.write!(
      manifest,
      String.replace(
        File.read!(manifest),
        ~s(["base", "app", "nif"]),
        ~s(["base", "app", "nif", "unrelated"])
      )
    )

    lock = Path.join(workspace, "Cargo.lock")

    File.write!(
      lock,
      File.read!(lock) <>
        ~s(\n[[package]]\nname = "experiment-unrelated"\nversion = "0.1.0"\n)
    )

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxRwResourceFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RwShared"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    properties = File.read!(Path.join(@fixture, "RwResourceProperties.lean"))
    File.write!(Path.join(project, "RwShared/Properties.lean"), properties)

    common = [
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["rw-resource"]],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "RwShared.Extraction"
    ]

    required =
      ~w(RwShared.Properties.toggle_base RwShared.Properties.toggle_app
      RwShared.Properties.shared_cycle RwShared.Properties.unregistered RwShared.Properties.reject_registered)

    opts =
      common ++
        [
          roots: ["ownership_nif::rw_resource_cycle", "ownership_nif::rw_resource_reject"],
          proof_modules: ["RwShared.Properties"],
          required_properties: required
        ]

    result = Lynx.Rust.verify!(workspace, "ownership-nif", opts)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.contains?(&1.label, "compiler-certified no-drop payload")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "ownership-nif", opts).reports

    options =
      common ++
        [
          workspace: workspace,
          package: "ownership-nif",
          root_attribute: "lynx::rw_resource",
          proof_roots: ["ownership_nif::rw_resource_cycle"],
          only: [shared_new: 1, shared_toggle: 1, shared_read: 1, shared_checked: 2]
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert length(prepared.bindings.bindings) == 4

    nif_properties = File.read!(Path.join(@fixture, "RwResourceNifProperties.lean"))

    nif_properties =
      Enum.reduce(
        [
          {"__NEW__", "shared_new"},
          {"__TOGGLE__", "shared_toggle"},
          {"__READ__", "shared_read"},
          {"__CHECKED__", "shared_checked"}
        ],
        nif_properties,
        fn {placeholder, name}, text ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(text, placeholder, binding["lean_name"])
        end
      )

    File.write!(Path.join(project, "RwShared/NifProperties.lean"), nif_properties)

    nif_options =
      options ++
        [
          proof_modules: ["RwShared.Properties", "RwShared.NifProperties"],
          required_properties:
            required ++
              ~w(RwShared.Properties.facade_new RwShared.Properties.facade_toggle
        RwShared.Properties.facade_read RwShared.Properties.facade_checked
        RwShared.Properties.factory_next RwShared.Properties.toggle_next
        RwShared.Properties.read_next RwShared.Properties.checked_next)
        ]

    prepared = Lynx.Rustler.prepare!(nif_options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.map(prepared.bindings.bindings, &{&1["name"], &1["arity"], &1["flags"]})
           |> Enum.sort() == [
             {"shared_checked", 2, 1},
             {"shared_new", 1, 0},
             {"shared_read", 1, 0},
             {"shared_toggle", 1, 1}
           ]

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, nif_options[:proof_modules],
        required_properties: nif_options[:required_properties]
      )

    export = Path.join(tmp, "shared.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    adapter = hd(prepared.external.files)["preludes"] |> hd() |> Map.fetch!("source")
    assert adapter =~ "Lynx.NativeOwnedDrop.drop"
    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
    elixir = Path.join(workspace, "elixir")
    File.mkdir_p!(elixir)
    stub = Path.join(elixir, "native.ex")

    File.write!(
      stub,
      File.read!(Path.join(@fixture, "elixir/native.ex"))
      |> String.replace("LynxOwnershipFixture", "LynxRwResourceFixture")
      |> String.replace(
        "\nend\n",
        "\n  def shared_new(_value), do: :erlang.nif_error(:not_loaded)\n  def shared_update(_resource), do: :erlang.nif_error(:not_loaded)\n  def shared_toggle(_resource), do: :erlang.nif_error(:not_loaded)\n  def shared_read(_resource), do: :erlang.nif_error(:not_loaded)\n  def shared_checked(_value, _accepted), do: :erlang.nif_error(:not_loaded)\nend\n"
      )
    )

    Code.compile_file(stub)

    for value <- [false, true] do
      resource = apply(LynxRwResourceFixture.Native, :shared_new, [value])
      assert apply(LynxRwResourceFixture.Native, :shared_read, [resource]) == value
      assert apply(LynxRwResourceFixture.Native, :shared_toggle, [resource]) == !value
      assert apply(LynxRwResourceFixture.Native, :shared_read, [resource]) == !value
      assert apply(LynxRwResourceFixture.Native, :shared_toggle, [resource]) == value
      assert apply(LynxRwResourceFixture.Native, :shared_read, [resource]) == value

      assert catch_error(apply(LynxRwResourceFixture.Native, :shared_checked, [value, false])) ==
               :nif_panicked
    end

    assert_raise ArgumentError, fn -> apply(LynxRwResourceFixture.Native, :shared_read, [7]) end
    [{law_module, beam}] = Code.compile_file(Path.join(@fixture, "elixir/rw_resource_laws.ex"))

    for law <- ~w(initial_value shared_write two_writes accepted_request invalid_resource)a,
        do: assert(apply(law_module, law, []))

    law_export = Path.join(tmp, "shared-laws.export")
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, nif_options}, export: law_export)

    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 5

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, nif_options}),
             &(&1.status == :ok and &1.cached)
           )

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", law_export] ++ sandbox)

    assert status == 0, output

    property = Path.join(project, "RwShared/Properties.lean")

    for extra <- [
          "private axiom sharedTrust : False",
          "private theorem unfinishedShared : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(nif_options)
      end
    end

    File.write!(property, properties)
    wrong = String.replace(properties, "nativeRefCounter := 6", "nativeRefCounter := 5")
    refute wrong == properties
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(nif_options)
    end

    File.write!(property, properties)

    unrelated = Path.join(workspace, "unrelated/src/lib.rs")
    unrelated_source = File.read!(unrelated)

    unrelated_change =
      String.replace(unrelated_source, "\n    value\n", "\n    value.wrapping_add(1)\n")

    refute unrelated_change == unrelated_source
    File.write!(unrelated, unrelated_change)
    repeated = Lynx.Rustler.prepare!(nif_options)
    assert repeated.extraction.fingerprint == prepared.extraction.fingerprint
    assert Enum.all?(repeated.reports, &(&1.status == :ok and &1.cached))
    File.write!(unrelated, unrelated_source)

    base = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(base)

    changed =
      String.replace(
        original,
        "pub fn toggle(value: &mut bool) {\n    *value = !*value;",
        "pub fn toggle(value: &mut bool) {\n    *value = false;"
      )

    refute changed == original
    File.write!(base, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(nif_options)
    end

    File.write!(base, original)
    assert Enum.all?(Lynx.Rustler.prepare!(nif_options).reports, &(&1.status == :ok))
    File.write!(Path.join(tmp, "adapter.lean"), adapter)
  end
end
