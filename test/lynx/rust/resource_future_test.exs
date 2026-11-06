defmodule Lynx.Rust.ResourceFutureTest do
  use ExUnit.Case
  alias Lynx.Rust.{NativeLifetimes, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "owned-captures-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-captures backend")

  @tag :tmp_dir
  test "proves resource capture transfer, cancellation and cross-crate resumed mutation", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "ResourceAwait"))
    property = Path.join(project, "ResourceAwait/Properties.lean")
    original = File.read!(Path.join(@fixture, "NativeResourceFuture.lean"))
    File.write!(property, original)

    File.cp!(
      Path.join(@fixture, "NativeResourceFutureCritical.lean"),
      Path.join(project, "ResourceAwait/Critical.lean")
    )

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::resource_suspending"],
      futures: :cancelling,
      execution: :runtime,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "ResourceAwait.Extraction",
      proof_modules: ["ResourceAwait.Critical", "ResourceAwait.Properties"],
      required_properties:
        ["ResourceAwait.Critical.increment_spec", "ResourceAwait.Critical.critical_state_next"] ++
          Enum.map(
            ~w(initial_state release_next drop_unstarted first_pending_next cancel_pending completed_drop update_next resume_next suspend_then_cancel missing_capture missing_saved_owner),
            &("ResourceAwait.Properties." <> &1)
          )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.implementations,
             &String.ends_with?(&1.lean_name, "resource_suspending.closure.drop_owned")
           )

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))
    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    audit = result.extraction.audit

    coroutine =
      Enum.find(audit.translated["type_decls"], fn type ->
        type && List.last(type["item_meta"]["name"]) == %{"Builtin" => ["Closure", 0]}
      end)

    attributes = coroutine["item_meta"]["attr_info"]["attributes"]

    evidence =
      Enum.find(
        attributes,
        &match?(%{"Unknown" => %{"path" => "lynx::coroutine_storage_v2"}}, &1)
      )

    assert %{"state" => 2, "states" => [[0, 1], [], [], [3, 4, 5, 6]]} =
             JSON.decode!(evidence["Unknown"]["args"])

    for invalid <- [
          attributes ++ [evidence],
          Enum.map(attributes, fn item ->
            if item == evidence,
              do:
                put_in(
                  item,
                  ["Unknown", "args"],
                  JSON.encode!(%{"state" => 2, "states" => [[], [], [], [3, 4, 5, 6]]})
                ),
              else: item
          end),
          Enum.map(attributes, fn item ->
            if item == evidence,
              do:
                put_in(
                  item,
                  ["Unknown", "args"],
                  JSON.encode!(%{"state" => 2, "states" => [[0, 1], [], [], [0, 3, 4, 5, 6]]})
                ),
              else: item
          end)
        ] do
      translated =
        update_in(audit.translated, ["type_decls"], fn types ->
          Enum.map(types, fn type ->
            if type && type["def_id"] == coroutine["def_id"],
              do: put_in(type, ["item_meta", "attr_info", "attributes"], invalid),
              else: type
          end)
        end)

      assert_raise CompileError, ~r/compiler coroutine/, fn ->
        NativeLifetimes.audit!(
          audit.functions,
          audit.external_calls,
          translated,
          audit.references
        )
      end
    end

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "resource-future.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom captureTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    false_property =
      String.replace(
        original,
        "(.ok (), reclaimed env 3 true)",
        "(.ok (), live env value 3 true)"
      )

    refute false_property == original
    File.write!(property, false_property)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)
    source = Path.join(workspace, "native/src/lib.rs")
    rust = File.read!(source)

    changed =
      String.replace(
        rust,
        "let _progress = effects_core::paused_counter(amount).await;\n    let changed = resource_locked_increment(&resource, amount);",
        "let _progress = effects_core::paused_counter(amount).await;\n    let changed = resource_locked_increment(&resource, amount.saturating_add(1));"
      )

    refute changed == rust
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end
end
