defmodule Lynx.Rust.IoErrorConcurrentTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for concurrent I/O error destruction proofs")

  @tag :tmp_dir
  test "consumes independently owned OS errors under every interleaving", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Errors"))
    property = Path.join(project, "Errors/Properties.lean")
    source = File.read!(Path.join(@fixture, "IoErrorConcurrent.lean"))
    File.write!(property, source)

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["io_protocol::discard_error_ack", "io_core::discard_io_error_implicit"],
      owned_drops: true,
      files: :regular,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Errors.Extraction",
      proof_modules: ["Errors.Properties"],
      required_properties: [
        "Errors.Properties.every_interleaving",
        "Errors.Properties.every_schedule"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "io_protocol::discard_error_ack" &&
               guarantee.theorem == "Errors.Properties.every_interleaving"
           end)

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :cross_crate_contract &&
               guarantee.rust_name == "io_protocol::discard_error_ack" &&
               guarantee.theorem == "Errors.Properties.every_interleaving"
           end)

    assert result.verification.owned_drops

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :rust_implementation &&
               guarantee.rust_name == "io_core::discard_io_error_implicit" &&
               guarantee.theorem == "Errors.Properties.every_interleaving"
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Lynx.Rust.Proofs.file!(
        result.extraction,
        options[:proof_modules]
      )

    export = Path.join(tmp, "errors.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    assert File.read!(export) =~ "every_interleaving"
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for invalid <- [
          String.replace(source, "env.nativeRefCounter == 3", "env.nativeRefCounter == 4"),
          source <> "\nprivate axiom uncheckedErrors : False\n",
          source <> "\nprivate theorem unfinishedErrors : False := by sorry\n"
        ] do
      refute invalid == source
      File.write!(property, invalid)
      assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end
    end

    File.write!(property, source)
    protocol = Path.join(workspace, "protocol/src/lib.rs")
    implementation = File.read!(protocol)

    broken =
      String.replace(
        implementation,
        "io_core::discard_io_error(error);\n    true",
        "io_core::discard_io_error(error);\n    false"
      )

    refute broken == implementation
    File.write!(protocol, broken)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", options)
    end

    File.write!(protocol, implementation)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
