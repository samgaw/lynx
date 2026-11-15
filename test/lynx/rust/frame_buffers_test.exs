defmodule Lynx.Rust.FrameBuffersTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @runtime_tools System.get_env("LYNX_NATIVE_BUFFER_DIR")
  @moduletag timeout: 900_000
  @tag skip: is_nil(@tools)
  @tag :tmp_dir
  test "proves exact owned frame consumption and rejection across crates", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "SplitBuffer"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    proof = Path.join(project, "SplitBuffer/Properties.lean")
    File.cp!(Path.join(@fixture, "FrameProperties.lean"), proof)

    options = [
      tools: @tools,
      mir: :optimized,
      roots: ["atomic_core::frames::split_buffer", "atomic_analysis::take_frame"],
      lean_project: project,
      module_prefix: "SplitBuffer.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["SplitBuffer.Properties"],
      required_properties:
        Enum.map(
          ~w(split_exact split_panic split_cutoff split_preserves_bytes short wrong_version truncated consumes_exact no_panic),
          &("SplitBuffer.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.ends_with?(&1.rust_name, "::split_off")
           )

    export = Path.join(tmp, "native.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    original = File.read!(proof)
    File.write!(proof, String.replace(original, "rest.val = tail := by", "rest.val = [] := by"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    end

    File.write!(proof, original)

    source = Path.join(workspace, "core/src/frames.rs")
    rust = File.read!(source)
    wrong = String.replace(rust, "input.split_off(position)", "input.split_off(0)")
    refute wrong == rust
    File.write!(source, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports
  end

  @tag skip: is_nil(@runtime_tools)
  @tag :tmp_dir
  test "proves parser panic exclusion in the native runtime", %{tmp_dir: tmp} do
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

    File.cp!(
      Path.join(@fixture, "FrameRuntimeProperties.lean"),
      Path.join(project, "FrameRuntime/Properties.lean")
    )

    options = [
      tools: @runtime_tools,
      execution: :runtime,
      owned_drops: true,
      branching: :duplicate,
      roots: ["atomic_core::frames::take_frame"],
      lean_project: project,
      module_prefix: "FrameRuntime.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["FrameRuntime.Properties"],
      required_properties: [
        "FrameRuntime.Properties.no_panic",
        "FrameRuntime.Properties.split_panic"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports

    export = Path.join(tmp, "native.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

    assert status == 0, output

    source = Path.join(workspace, "core/src/frames.rs")
    rust = File.read!(source)

    changed =
      String.replace(
        rust,
        "if input.len() < 3 {",
        "if input.len() < 3 { let _ = split_buffer(input, 3);"
      )

    refute changed == rust
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports
  end
end
