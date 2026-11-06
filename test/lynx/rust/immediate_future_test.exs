defmodule Lynx.Rust.ImmediateFutureTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "immediate-futures-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned immediate-futures-v1 backend")

  @tag :tmp_dir
  test "proves compiler future construction, cross-crate polling and completed-state panic", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Future"))
    property = Path.join(project, "Future/Properties.lean")
    original = File.read!(Path.join(@fixture, "NativeImmediateFuture.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::immediate_increment"],
      futures: :immediate,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Future.Extraction",
      proof_modules: ["Future.Properties"],
      required_properties:
        Enum.map(
          ~w(core_increment initial_state first_poll repoll_completed),
          &("Future.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract && row.theorem == "Future.Properties.first_poll" &&
               "Future.Properties.core_increment" in row.contracts_used
           end)

    assert Enum.any?(
             result.verification.external_models,
             &String.starts_with?(&1, "Unobserved task Context")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    export = Path.join(project, "future.export")

    file =
      Lynx.Rust.Proofs.file!(result.extraction, ["Future.Properties"],
        required_properties: options[:required_properties]
      )

    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom futureTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["Future.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(
      property,
      String.replace(original, "future.pointer.state = 1#u32", "future.pointer.state = 0#u32")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Future.Properties"])
    end

    File.write!(property, original)

    for root <- ["effects_native::async_increment", "effects_native::owned_immediate"] do
      assert_raise ArgumentError, ~r/Charon reported extraction errors/, fn ->
        Lynx.Rust.Extraction.describe!(
          result.context,
          @tools,
          [root],
          project,
          "Future.Unsupported",
          futures: :immediate
        )
      end
    end

    core = Path.join(workspace, "core/src/lib.rs")

    File.write!(
      core,
      String.replace(File.read!(core), "value.saturating_add(1)", "value.saturating_add(2)")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end
end
