defmodule Lynx.Rust.FileCommitTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned patched backend")

  @tag :tmp_dir
  test "creation and writing compose with durable publication and owning recovery", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Publish"))

    File.cp!(
      Path.join(@fixture, "PublishProperties.lean"),
      Path.join(project, "Publish/Properties.lean")
    )

    File.cp!(
      Path.join(@fixture, "NamedRecovery.lean"),
      Path.join(project, "Publish/NamedRecovery.lean")
    )

    File.cp!(
      Path.join(@fixture, "PayloadProperties.lean"),
      Path.join(project, "Publish/Payload.lean")
    )

    File.cp!(
      Path.join(@fixture, "WordRecovery.lean"),
      Path.join(project, "Publish/WordRecovery.lean")
    )

    File.cp!(
      Path.join(@fixture, "CommitProperties.lean"),
      Path.join(project, "Publish/Commit.lean")
    )

    property = Path.join(project, "Publish/CommitRejected.lean")
    File.cp!(Path.join(@fixture, "CommitRejected.lean"), property)
    original = File.read!(property)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      ~w(Publish.Commit.commit_contract Publish.Commit.commit_recovery Publish.Commit.write_prefix
      Publish.Commit.Rejected.write_error Publish.Commit.Rejected.zero_write
      Publish.Commit.Rejected.short_write)

    options = [
      roots: [
        "io_protocol::commit_word",
        "io_protocol::publish_file",
        "io_protocol::recover_named_word",
        "io_protocol::open_readonly",
        "io_protocol::sync_directory",
        "io_core::synchronize"
      ],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      module_prefix: "Publish.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: [
        "Publish.Properties",
        "Publish.Payload",
        "Publish.NamedRecovery",
        "Publish.WordRecovery",
        "Publish.Commit",
        "Publish.CommitRejected"
      ],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.contains?(&1.rust_name, "sync_all")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "commit.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom commitTrust : False",
          "private theorem unfinishedCommit : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    wrong =
      String.replace(
        original,
        "(.ok (.Ok false),world (prefixBytes value 1) 1 .nil true)",
        "(.ok (.Ok true),world (prefixBytes value 1) 1 .nil true)"
      )

    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)

    source = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(source)

    for {before, after_} <- [
          {"&value.to_le_bytes()", "&value.to_be_bytes()"},
          {"Ok(2) =>", "Ok(1) =>"}
        ] do
      changed = String.replace(rust, before, after_)
      refute changed == rust
      File.write!(source, changed)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      assert error.message =~ "Publish/Commit.lean:" or
               error.message =~ "Publish/CommitRejected.lean:"
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
