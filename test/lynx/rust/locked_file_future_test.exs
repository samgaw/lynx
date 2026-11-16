defmodule Lynx.Rust.LockedFileFutureTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_FILE_AWAIT_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_FILE_AWAIT_DIR for guarded shared file future proofs")

  @tag :tmp_dir
  test "verifies borrowed mutex file futures independently of Rustler", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "LockedAwait"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    for {source, target} <- [
          {"LockedAwaitProperties.lean", "Properties.lean"},
          {"LockedAwaitIoProperties.lean", "Io.lean"},
          {"NativeNoPanicProperties.lean", "Safety.lean"}
        ],
        do: File.cp!(Path.join(@fixture, source), Path.join(project, "LockedAwait/" <> target))

    properties =
      Enum.map(
        ~w(constructor unstarted_cleanup suspended_cleanup completed_cleanup yield_pending yield_ready resume_contract first_pending_contract caller_contract no_panic caller_success_prefix caller_error_prefix),
        &("LockedAwait.Properties." <> &1)
      ) ++
        Enum.map(
          ~w(partial_prefix error_prefix partial_result error_result),
          &("LockedAwait.Io." <> &1)
        )

    options = [
      roots: ~w(io_protocol::locked_suspended_write io_protocol::poll_locked_write),
      tools: @tools,
      execution: :runtime,
      files: :regular,
      futures: :cancelling,
      owned_drops: true,
      branching: :duplicate,
      lean_project: project,
      module_prefix: "LockedAwait.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["LockedAwait.Properties", "LockedAwait.Io", "LockedAwait.Safety"],
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
    [prefix, writer] = String.split(valid, "pub async fn locked_suspended_write(", parts: 2)

    wrong_error =
      String.replace(writer, "            Err(1)", "            Err(2)", global: false)

    refute writer == wrong_error
    File.write!(source, prefix <> "pub async fn locked_suspended_write(" <> wrong_error)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", options)
    end

    File.write!(source, valid)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
