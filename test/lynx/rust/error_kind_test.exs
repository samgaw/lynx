defmodule Lynx.Rust.ErrorKindTest do
  use ExUnit.Case
  alias Lynx.Rust.{LibraryHelpers, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for actual ErrorKind proofs")

  @tag :tmp_dir
  test "proves standard error classification across crates using actual enum constants", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "IoKinds"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    property = Path.join(project, "IoKinds/Properties.lean")
    original = File.read!(Path.join(@fixture, "ErrorKindProperties.lean"))
    File.write!(property, original)

    options = [
      tools: @tools,
      sysroot: :full_mir,
      roots: ["io_protocol::truncated_input"],
      lean_project: project,
      module_prefix: "IoKinds.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["IoKinds.Properties"],
      required_properties:
        ~w(IoKinds.Properties.core_spec IoKinds.Properties.composition IoKinds.Properties.interruption)
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    audit = result.extraction.audit
    [helper] = Enum.filter(audit.functions, &LibraryHelpers.selected?(&1, audit.translated))
    refute Map.has_key?(audit.external_calls, helper["def_id"])

    for altered <- [
          Map.put(helper, "body", "Opaque"),
          put_in(helper, ["signature", "is_unsafe"], true),
          put_in(helper, ["signature", "inputs"], [])
        ] do
      refute LibraryHelpers.selected?(altered, audit.translated)
    end

    impl = helper["src"]["TraitImpl"]["impl_ref"]["id"]

    missing =
      Map.update!(audit.translated, "trait_impls", fn implementations ->
        Enum.map(implementations, fn
          %{"def_id" => ^impl} = item -> Map.put(item, "methods", [])
          other -> other
        end)
      end)

    refute LibraryHelpers.selected?(helper, missing)

    export = Path.join(tmp, "kinds.export")

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom hidden_kind : False",
          "private theorem unfinished_kind : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/proof audit failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end
    end

    File.write!(property, original)

    for {relative, before, replacement} <- [
          {"core/src/lib.rs", "TRUNCATED_INPUT: io::ErrorKind = io::ErrorKind::UnexpectedEof",
           "TRUNCATED_INPUT: io::ErrorKind = io::ErrorKind::Interrupted"},
          {"protocol/src/lib.rs", "io_core::is_truncated(kind)", "!io_core::is_truncated(kind)"}
        ] do
      path = Path.join(workspace, relative)
      rust = File.read!(path)
      changed = String.replace(rust, before, replacement)
      refute changed == rust
      File.write!(path, changed)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      assert error.message =~ "IoKinds/Properties.lean:"
      File.write!(path, rust)
    end

    core = Path.join(workspace, "core/src/lib.rs")
    protocol = Path.join(workspace, "protocol/src/lib.rs")
    core_source = File.read!(core)
    protocol_source = File.read!(protocol)

    File.write!(
      core,
      core_source <>
        """

        pub enum DroppingKind { Only }
        impl Drop for DroppingKind {
            fn drop(&mut self) { panic!("observable enum destruction"); }
        }
        pub const DROPPING: DroppingKind = DroppingKind::Only;
        pub fn cleanup_kind() -> bool {
            let kind = DROPPING;
            matches!(kind, DroppingKind::Only)
        }
        """
    )

    File.write!(
      protocol,
      protocol_source <>
        "\npub fn cleanup_kind() -> bool { io_core::cleanup_kind() }\n"
    )

    assert_raise CompileError, ~r/structural drop erasure rejected/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "io-protocol",
        Keyword.put(options, :roots, ["io_protocol::cleanup_kind"])
      )
    end

    File.write!(core, core_source)
    File.write!(protocol, protocol_source)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
