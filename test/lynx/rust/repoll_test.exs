defmodule Lynx.Rust.RepollTest do
  use ExUnit.Case
  alias Lynx.Rust.Project
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "pin-as-mut-v1")
  unless @available, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned pin-as-mut backend")

  @tag :tmp_dir
  test "proves actual Rust repolling composes mutation and resource cleanup", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for name <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Macro"))

    for {source, target} <- [
          {"NativeResourceFutureCritical.lean", "Critical.lean"},
          {"NativeResourceFuture.lean", "Properties.lean"},
          {"NativeRepoll.lean", "Completion.lean"}
        ] do
      File.write!(
        Path.join(project, "Macro/" <> target),
        File.read!(Path.join(@fixture, source)) |> String.replace("ResourceAwait", "Macro")
      )
    end

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::finish_resource"],
      futures: :cancelling,
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      module_prefix: "Macro.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Macro.Critical", "Macro.Properties", "Macro.Completion"],
      required_properties: ["Macro.Completion.completion"]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract && &1.theorem == "Macro.Completion.completion")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "repoll.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    property = Path.join(project, "Macro/Completion.lean")
    original = File.read!(property)

    for extra <- [
          "private axiom repollTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    false_property = String.replace(original, ".ok (.Ready changed,", ".ok (.Pending,")
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
        "std::task::Poll::Pending => future.as_mut().poll(context)",
        "std::task::Poll::Pending => std::task::Poll::Pending"
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
