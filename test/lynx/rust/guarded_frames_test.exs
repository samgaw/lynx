defmodule Lynx.Rust.GuardedFramesTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_BUFFER_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_NATIVE_BUFFER_DIR for guarded Rust composition")

  @tag :tmp_dir
  test "links a protected parser proof to an actual guarded cross-crate caller", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "FrameRuntime"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    for {source, target} <- [
          {"FrameRuntimeProperties.lean", "Properties.lean"},
          {"GuardedFramesProperties.lean", "GuardedProperties.lean"}
        ],
        do: File.cp!(Path.join(@fixture, source), Path.join(project, "FrameRuntime/" <> target))

    options = [
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      branching: :duplicate,
      roots: ["atomic_analysis::parse_frame"],
      lean_project: project,
      module_prefix: "FrameRuntime.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["FrameRuntime.Properties", "FrameRuntime.GuardedProperties"],
      required_properties: ["FrameRuntime.GuardedProperties.parse_contract"],
      nonpanicking: [{"atomic_core::frames::take_frame", "FrameRuntime.Properties.no_panic"}]
    ]

    result = Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))
    export = Path.join(tmp, "native.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    assert_raise CompileError, ~r/drop|borrowed native guard/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", Keyword.delete(options, :nonpanicking))
    end
  end
end
