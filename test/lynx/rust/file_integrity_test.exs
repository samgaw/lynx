defmodule Lynx.Rust.FileIntegrityTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "tuple-back-projections-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned tuple-back-projections backend")

  @tag :tmp_dir
  test "checks actual cross-crate fresh-record integrity and recovery", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Record"))

    sources = [
      {"Properties", [{"Disk", "Record"}]},
      {"ReadProperties",
       [
         {"Read.Properties", "Record.Properties"},
         {"Read.ReadProperties", "Record.ReadProperties"}
       ]},
      {"RecoveryProperties",
       [
         {"Recovery.Properties", "Record.Properties"},
         {"Recovery.ReadProperties", "Record.ReadProperties"},
         {"Recovery.Extraction", "Record.Extraction"},
         {"Recovery.RecoveryProperties", "Record.RecoveryProperties"}
       ]},
      {"IntegrityProperties", []}
    ]

    for {module, replacements} <- sources do
      source = File.read!(Path.join(@fixture, module <> ".lean"))

      source =
        Enum.reduce(replacements, source, fn {old, new}, text ->
          String.replace(text, old, new)
        end)

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), source)
    end

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: [
        "io_protocol::recover_record",
        "io_protocol::write_record",
        "io_protocol::recover_word"
      ],
      execution: :runtime,
      files: :regular,
      tools: @tools,
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: Enum.map(sources, fn {name, _} -> "Record." <> name end),
      required_properties:
        Enum.map(
          ~w(encode_spec decode_spec decode_layout write_record_ready torn_decode record_ready record_torn four_reads recover_four recover_torn_default),
          &("Record.IntegrityProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert [
             %{
               "status" => :modelled,
               "implementation_verified" => false,
               "lean_name" => "Aeneas.Std.core.num.U16.MAX"
             }
           ] = result.verification.constants

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "initializer not implementation verified")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Record.IntegrityProperties.recover_torn_default")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "integrity.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    property = Path.join(project, "Record/IntegrityProperties.lean")
    original = File.read!(property)

    for extra <- [
          "private axiom integrityTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(property, original)
    end

    source = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(source)

    for broken <- [
          String.replace(rust, "Some(value)", "Some(inverse)"),
          String.replace(rust, "(!value).to_le_bytes()", "value.to_le_bytes()")
        ] do
      refute broken == rust
      File.write!(source, broken)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      assert error.message =~ "Record/IntegrityProperties.lean:"
      File.write!(source, rust)
    end

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
