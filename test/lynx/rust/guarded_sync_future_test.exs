defmodule Lynx.Rust.GuardedSyncFutureTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_FILE_AWAIT_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_FILE_AWAIT_DIR for guarded synchronization future proofs")

  @tag :tmp_dir
  test "verifies guarded synchronization and cancellation independently of Rustler", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "GuardedSync"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    for {source, target} <- [
          {"GuardedSyncProperties.lean", "Properties.lean"},
          {"GuardedSyncIoProperties.lean", "Io.lean"}
        ],
        do: File.cp!(Path.join(@fixture, source), Path.join(project, "GuardedSync/" <> target))

    properties =
      Enum.map(
        ~w(constructor unstarted_cleanup suspended_cleanup completed_cleanup yield_pending yield_ready synchronize_contract resume_contract first_pending_contract caller_contract synchronize_no_panic no_panic),
        &("GuardedSync.Properties." <> &1)
      ) ++
        Enum.map(
          ~w(cancel_and_sync_outcomes every_completed_call write_error_skips_sync),
          &("GuardedSync.Io." <> &1)
        )

    options = [
      roots: ~w(io_protocol::locked_suspended_sync io_protocol::poll_locked_sync),
      tools: @tools,
      execution: :runtime,
      files: :regular,
      futures: :cancelling,
      owned_drops: true,
      branching: :duplicate,
      lean_project: project,
      module_prefix: "GuardedSync.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["GuardedSync.Properties", "GuardedSync.Io"],
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

    export = Path.join(tmp, "guarded.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(workspace, "protocol/src/lib.rs")
    valid = File.read!(source)
    [prefix, helper] = String.split(valid, "fn synchronize_written(", parts: 2)

    # The actual first-party implementation must perform synchronization before
    # its successful acknowledgement; a proof for the old body cannot be reused.
    bypassed =
      String.replace(
        helper,
        "        Ok(count) => match",
        "        Ok(2) => Ok(2),\n        Ok(count) => match",
        global: false
      )

    refute helper == bypassed
    File.write!(source, prefix <> "fn synchronize_written(" <> bypassed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", options)
    end

    File.write!(source, valid)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
