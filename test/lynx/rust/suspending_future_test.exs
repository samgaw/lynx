defmodule Lynx.Rust.SuspendingFutureTest do
  use ExUnit.Case
  alias Lynx.Rust.{LibraryHelpers, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               Enum.all?(
                 ~w(suspending-futures-v1 undefined-behavior-v1),
                 &String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), &1)
               )
  unless @available,
    do:
      @moduletag(
        skip: "set LYNX_AENEAS_DIR to the pinned suspending-futures/undefined-behavior backend"
      )

  @tag :tmp_dir
  test "proves actual await suspension, saved state and cross-crate resumption", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Suspend"))
    property = Path.join(project, "Suspend/Properties.lean")
    original = File.read!(Path.join(@fixture, "NativeSuspendingFuture.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::suspended_increment"],
      futures: :suspending,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Suspend.Extraction",
      proof_modules: ["Suspend.Properties"],
      required_properties:
        Enum.map(
          ~w(internal_initial_state core_increment callee_pending callee_ready initial_state first_pending_next first_pending resume_ready missing_saved_slot exhaustion_not_catchable repoll_completed two_polls),
          &("Suspend.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports
    assert result.verification.futures == :suspending

    assert Enum.any?(
             result.verification.external_models,
             &String.starts_with?(&1, "Compiler coroutine saved-slot interpretation")
           )

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Suspend.Properties.first_pending_next" &&
               "Suspend.Properties.callee_pending" in row.contracts_used
           end)

    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert Enum.any?(
             result.verification.implementations,
             &String.ends_with?(&1.lean_name, "suspended_increment.closure.poll")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    translated = result.extraction.audit.translated

    helpers =
      Enum.filter(translated["fun_decls"], &(&1 && LibraryHelpers.selected?(&1, translated)))

    assert length(helpers) == 2

    [identity] =
      Enum.filter(
        helpers,
        &(&1["item_meta"]["name"] |> List.last() == %{"Ident" => ["into_future", 0]})
      )

    refute LibraryHelpers.selected?(Map.put(identity, "body", "Opaque"), translated)

    refute LibraryHelpers.selected?(
             put_in(identity, ["signature", "is_unsafe"], true),
             translated
           )

    file =
      Proofs.file!(result.extraction, ["Suspend.Properties"],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "suspend.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom nativeTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, ["Suspend.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    broken = String.replace(original, "value, 3#u32, some", "value, 1#u32, some", global: false)
    refute broken == original
    File.write!(property, broken)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, ["Suspend.Properties"])
    end

    File.write!(property, original)

    core = Path.join(workspace, "core/src/lib.rs")
    original_core = File.read!(core)

    for {before, after_text} <- [
          {"this.waiting = false;", "this.waiting = true;"},
          {"context.waker().wake_by_ref();", "let _wake_identity = context.waker();"}
        ] do
      File.write!(core, String.replace(original_core, before, after_text))

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "effects-native", options)
      end
    end

    File.write!(core, original_core)

    assert_raise ArgumentError, ~r/Saved future fields requiring drop/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "effects-native",
        Keyword.put(options, :roots, ["effects_native::owned_suspending"])
      )
    end
  end
end
