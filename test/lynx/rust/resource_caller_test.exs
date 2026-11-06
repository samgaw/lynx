defmodule Lynx.Rust.ResourceCallerTest do
  use ExUnit.Case
  alias Lynx.Rust.{NativeLifetimes, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "pin-macro-v1")
  unless @available, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned pin-macro backend")

  @tag :tmp_dir
  test "proves actual Rust callers complete and cancel resource futures with compiler cleanup", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Macro"))

    for {source, target} <- [
          {"NativeResourceFutureCritical.lean", "Critical.lean"},
          {"NativeResourceFuture.lean", "Properties.lean"}
        ] do
      File.write!(
        Path.join(project, "Macro/" <> target),
        File.read!(Path.join(@fixture, source)) |> String.replace("ResourceAwait", "Macro")
      )
    end

    property = Path.join(project, "Macro/Caller.lean")
    original = File.read!(Path.join(@fixture, "NativeResourceCaller.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::poll_ready_resource", "effects_native::poll_cancel_resource"],
      futures: :cancelling,
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      module_prefix: "Macro.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Macro.Critical", "Macro.Properties", "Macro.Caller"],
      required_properties:
        ["Macro.Critical.increment_spec", "Macro.Critical.critical_state_next"] ++
          Enum.map(
            ~w(initial_state release_next drop_unstarted first_pending_next cancel_pending completed_drop update_next resume_next suspend_then_cancel missing_capture missing_saved_owner),
            &("Macro.Properties." <> &1)
          ) ++
          Enum.map(
            ~w(caller_contract caller_cancellation ready_poll_contract completed_cleanup ready_caller_contract caller_completion),
            &("Macro.Caller." <> &1)
          )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.implementations,
             &String.ends_with?(&1.lean_name, "resource_immediate.closure.poll")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract && &1.theorem == "Macro.Caller.caller_completion")
           )

    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    audit = result.extraction.audit

    poll =
      Enum.find(audit.functions, fn function ->
        List.last(function["item_meta"]["name"]) == %{"Ident" => ["poll", 0]} &&
          Enum.member?(function["item_meta"]["name"], %{"Ident" => ["resource_immediate", 0]})
      end)

    refute is_nil(poll)

    panicking =
      put_in(poll, ["body", "Structured", "body", "statements"], [
        %{"kind" => %{"Panic" => %{"on_unwind" => %{"statements" => []}}}}
      ])

    ordinary =
      update_in(
        poll,
        ["item_meta", "name"],
        &List.replace_at(&1, -1, %{"Ident" => ["ordinary", 0]})
      )

    for altered <- [panicking, ordinary] do
      functions =
        Enum.map(audit.functions, fn function ->
          if function["def_id"] == poll["def_id"], do: altered, else: function
        end)

      assert_raise CompileError, ~r/native owner lifetime|borrowed owned-future state/, fn ->
        NativeLifetimes.audit!(
          functions,
          audit.external_calls,
          audit.translated,
          audit.references
        )
      end
    end

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "caller.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom callerTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    false_property =
      String.replace(
        original,
        "(.ok (.Pending, ⟨⟨0⟩⟩), reclaimed env 3 true)",
        "(.ok (.Ready false, ⟨⟨0⟩⟩), reclaimed env 3 true)"
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
        "resource_locked_increment(&resource, amount);\n    resource_release(resource);",
        "resource_locked_increment(&resource, amount.saturating_add(1));\n    resource_release(resource);"
      )

    refute changed == rust
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    retained =
      String.replace(
        rust,
        "std::pin::pin!(resource_immediate(resource, amount)).poll(context)",
        "let retained = resource.clone();\n    let result = std::pin::pin!(resource_immediate(resource, amount)).poll(context);\n    resource_release(retained);\n    result"
      )

    refute retained == rust
    File.write!(source, retained)

    # The added owner's unwind destructor is rejected before lifetime analysis.
    assert_raise CompileError, ~r/Rust structural drop erasure rejected/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end
end
