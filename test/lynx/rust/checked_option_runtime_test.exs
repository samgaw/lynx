defmodule Lynx.Rust.CheckedOptionRuntimeTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "lynx-result-monad-v1"
               )
  unless @available, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the runtime toolchain")

  @tag :tmp_dir
  test "preserves checked Some/None behavior in the native runtime interpretation", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RuntimeTry"))
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    source =
      File.read!(Path.join(@fixture, "proofs/RustWorkspace/CheckedInternal.lean"))
      |> String.replace("RustWorkspace.CheckedInternalExtraction", "RuntimeTry.Extraction")
      |> String.replace("RustWorkspace.CheckedInternal", "RuntimeTry.Properties")
      |> String.replace("RustWorkspace.NativeTry", "RuntimeTry.NativeTry")
      |> String.replace("RustM.ok", "Lynx.NativeM.ok")
      |> String.replace(", bind_ok]", "]")
      |> String.replace(", lift]", ", Lynx.NativeM.lift, Lynx.NativeM.ok]")

    property = Path.join(project, "RuntimeTry/Properties.lean")
    File.write!(property, source)

    options = [
      roots: ["experiment_analysis::analyse"],
      tools: @tools,
      execution: :runtime,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "RuntimeTry.Extraction",
      proof_modules: ["RuntimeTry.Properties"],
      required_properties:
        Enum.map(~w(core_spec caller_spec output_spec), &("RuntimeTry.Properties." <> &1))
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports
    assert result.verification.execution == :runtime

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(project, "runtime-try.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    model = Path.join(project, "RuntimeTry/NativeTry.lean")
    original_model = File.read!(model)

    for extra <- [
          "private axiom tryTrust : False",
          "private theorem unfinishedTry : True := by sorry"
        ] do
      File.write!(model, original_model <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["RuntimeTry.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(model, original_model)
    Lynx.Rust.Project.build!(project, ["RuntimeTry.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file])
  end
end
