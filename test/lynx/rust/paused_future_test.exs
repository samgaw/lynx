defmodule Lynx.Rust.PausedFutureTest do
  use ExUnit.Case
  alias Lynx.Rust.{LibraryHelpers, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               Enum.all?(
                 ~w(pin-borrow-transfer-v1 workspace-roots-v1),
                 &String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), &1)
               )
  unless @available,
    do:
      @moduletag(
        skip: "set LYNX_AENEAS_DIR to the pinned borrow-transfer/workspace-roots backend"
      )

  @tag :tmp_dir
  test "proves retained Pending state, later completion and an independent dependency root", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Poll"))
    property = Path.join(project, "Poll/Properties.lean")
    original = File.read!(Path.join(@fixture, "NativePausedFuture.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::poll_paused", "effects_core::paused_counter"],
      futures: :immediate,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Poll.Extraction",
      proof_modules: ["Poll.Properties"],
      required_properties:
        Enum.map(
          ~w(initial_state core_increment callee_pending callee_ready caller_pending no_early_completion two_polls),
          &("Poll.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract && row.theorem == "Poll.Properties.two_polls" &&
               "Poll.Properties.callee_ready" in row.contracts_used
           end)

    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    translated = result.extraction.audit.translated

    [getter] =
      Enum.filter(translated["fun_decls"], &(&1 && LibraryHelpers.selected?(&1, translated)))

    assert Enum.any?(
             result.verification.implementations,
             &(&1.source_kind == :included_library_helper)
           )

    copy_getter =
      update_in(getter, ["body", "Structured", "body", "statements"], fn statements ->
        Enum.map(statements, fn
          %{"kind" => %{"Assign" => [dest, %{"Use" => [%{"Move" => place}, "No"]}]}} = statement ->
            put_in(statement, ["kind", "Assign"], [dest, %{"Use" => [%{"Copy" => place}, "No"]}])

          statement ->
            statement
        end)
      end)

    for invalid <- [
          copy_getter,
          put_in(getter, ["signature", "is_unsafe"], true),
          Map.put(getter, "body", "Opaque"),
          put_in(getter, ["generics", "trait_clauses"], [])
        ] do
      refute LibraryHelpers.selected?(invalid, translated)
    end

    file =
      Proofs.file!(result.extraction, ["Poll.Properties"],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "poll.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom pollTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, ["Poll.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(
      property,
      String.replace(
        original,
        "RustM.ok (core.task.poll.Poll.Pending",
        "RustM.ok (core.task.poll.Poll.Ready 0#u64",
        global: false
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, ["Poll.Properties"])
    end

    File.write!(property, original)

    core = Path.join(workspace, "core/src/lib.rs")

    File.write!(
      core,
      String.replace(File.read!(core), "this.waiting = false;", "this.waiting = true;")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end
end
