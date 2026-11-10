defmodule Lynx.Rustler.RwContentionTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_RWLOCK_DIR")
  @moduletag timeout: 2_700_000
  unless @tools, do: @moduletag(skip: "set LYNX_RWLOCK_DIR for contending resource writers")

  @tag :tmp_dir
  test "actual resource writers preserve both updates under every logical schedule", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxRwContentionFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RwShared"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../rust_workspace/proofs/.lake/packages", @fixture),
      Path.join(project, ".lake/packages")
    )

    for {fixture, name} <- [
          {"RwResourceProperties.lean", "Properties"},
          {"RwContentionProperties.lean", "Contention"},
          {"RwContentionModelProperties.lean", "ContentionModel"}
        ],
        do: File.cp!(Path.join(@fixture, fixture), Path.join(project, "RwShared/#{name}.lean"))

    required = ~w(RwShared.Properties.toggle_base RwShared.Properties.toggle_app
      RwShared.Properties.shared_cycle RwShared.Properties.unregistered RwShared.Properties.reject_registered
      RwShared.Contention.every_interleaving RwShared.Contention.every_schedule)
    proofs = ["RwShared.Properties", "RwShared.Contention", "RwShared.ContentionModel"]

    common = [
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["rw-resource"]],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "RwShared.Extraction",
      proof_modules: proofs,
      required_properties: required
    ]

    internal =
      common ++
        [
          roots: [
            "ownership_nif::rw_resource_cycle",
            "ownership_nif::rw_resource_reject",
            "ownership_nif::rw_resource_clone",
            "ownership_nif::rw_resource_update",
            "ownership_nif::rw_resource_read"
          ]
        ]

    result = Lynx.Rust.verify!(workspace, "ownership-nif", internal)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "ownership-nif", internal).reports

    options =
      common ++
        [
          workspace: workspace,
          package: "ownership-nif",
          root_attribute: "lynx::rw_resource",
          proof_roots: ["ownership_nif::rw_resource_cycle", "ownership_nif::rw_resource_clone"],
          only: [shared_new: 1, shared_update: 1, shared_read: 1]
        ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [%{"name" => "shared_update", "rust_name" => "rw_update", "arity" => 1, "flags" => 1}] =
             Enum.filter(prepared.bindings.bindings, &(&1["name"] == "shared_update"))

    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.any?(
             prepared.verification.unverified_external_calls,
             &String.contains?(&1.label, "queued writers")
           )

    file = Lynx.Rust.Proofs.file!(prepared.extraction, proofs, required_properties: required)
    export = Path.join(tmp, "contention.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
    File.mkdir_p!(Path.join(workspace, "elixir"))
    stub = Path.join(workspace, "elixir/native.ex")

    File.write!(
      stub,
      File.read!(Path.join(@fixture, "elixir/native.ex"))
      |> String.replace("LynxOwnershipFixture", "LynxRwContentionFixture")
      |> String.replace("\nend\n", """
      \n  def shared_new(_value), do: :erlang.nif_error(:not_loaded)
        def shared_update(_resource), do: :erlang.nif_error(:not_loaded)
        def shared_toggle(_resource), do: :erlang.nif_error(:not_loaded)
        def shared_read(_resource), do: :erlang.nif_error(:not_loaded)
        def shared_checked(_value, _accepted), do: :erlang.nif_error(:not_loaded)
      end
      """)
    )

    Code.compile_file(stub)

    assert_raise ArgumentError, fn ->
      apply(LynxRwContentionFixture.Native, :shared_update, [7])
    end

    [{law_module, beam}] = Code.compile_file(Path.join(@fixture, "elixir/rw_contention_laws.ex"))
    assert apply(law_module, :competing_updates, [])
    law_export = Path.join(tmp, "contention-laws.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 4096],
        export: law_export
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 1

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", law_export] ++ sandbox)

    assert status == 0, output

    assert Enum.all?(
             Lynx.Laws.verify([beam],
               native: {Lynx.Rustler, options},
               options: [maxHeartbeats: 16_000_000, maxRecDepth: 4096]
             ),
             &(&1.status == :ok and &1.cached)
           )

    model = Path.join(project, "RwShared/ContentionModel.lean")
    model_source = File.read!(model)

    for extra <- [
          "private axiom contentionTrust : False",
          "private theorem unfinishedContention : True := by sorry"
        ] do
      File.write!(model, model_source <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(model, model_source)
    property = Path.join(project, "RwShared/Contention.lean")
    correct = File.read!(property)
    incorrect = String.replace(correct, "result == value", "result != value")
    refute incorrect == correct
    File.write!(property, incorrect)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert error.message =~ "RwShared.Contention"
    File.write!(property, correct)
    original = File.read!(source)
    [prefix, worker] = String.split(original, "pub fn rw_resource_update", parts: 2)

    changed =
      prefix <>
        "pub fn rw_resource_update" <>
        String.replace(worker, "ownership_app::toggle(&mut writer);", "*writer = true;",
          global: false
        )

    refute changed == original
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert error.message =~ "RwShared.Contention"
    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
