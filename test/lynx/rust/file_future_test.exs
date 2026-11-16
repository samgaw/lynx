defmodule Lynx.Rust.FileFutureTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_FILE_AWAIT_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_FILE_AWAIT_DIR for driven file future proofs")

  @tag :tmp_dir
  test "drives actual file futures through wake consumption, cancellation and poll cutoffs", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "FileAwait"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    for {source, target} <- [
          {"FileAwaitProperties.lean", "Properties.lean"},
          {"FileAwaitTask.lean", "Task.lean"}
        ],
        do: File.cp!(Path.join(@fixture, source), Path.join(project, "FileAwait/" <> target))

    properties =
      Enum.map(
        ~w(driven_file_cleanup every_driven_exit one_poll_cutoff),
        &("FileAwait.Task." <> &1)
      )

    options = [
      roots: ~w(io_protocol::suspended_write io_protocol::poll_write),
      tools: @tools,
      execution: :runtime,
      files: :regular,
      futures: :cancelling,
      owned_drops: true,
      branching: :duplicate,
      lean_project: project,
      module_prefix: "FileAwait.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["FileAwait.Properties", "FileAwait.Task"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports
    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: properties
      )

    export = Path.join(tmp, "task.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
