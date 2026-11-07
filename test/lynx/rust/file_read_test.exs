defmodule Lynx.Rust.FileReadTest do
  use ExUnit.Case
  alias Lynx.Rust.{ArrayModels, FileModels, IndexModels, Project, Proofs}
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
  test "proves a two-crate file parser and rejects endian and EOF violations", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Read"))

    File.write!(
      Path.join(project, "Read/Properties.lean"),
      File.read!(Path.join(@fixture, "Properties.lean")) |> String.replace("Disk", "Read")
    )

    property = Path.join(project, "Read/ReadProperties.lean")
    original = File.read!(Path.join(@fixture, "ReadProperties.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["io_protocol::read_word", "io_protocol::write_then_sync"],
      execution: :runtime,
      files: :regular,
      tools: @tools,
      lean_project: project,
      module_prefix: "Read.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Read.Properties", "Read.ReadProperties"],
      required_properties:
        Enum.map(
          ~w(read_next parser_ready parser_success parser_first_eof parser_second_eof parser_first_error parser_second_error),
          &("Read.ReadProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Read.ReadProperties.parser_success")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    # Check admission against the actual compiler metadata, including rejection of
    # unsafe signatures, changed trait identities and missing method dependencies.
    audit = result.extraction.audit

    selected =
      for f <- audit.external_functions,
          resolver <- [ArrayModels, FileModels, IndexModels],
          model = resolver.resolve(f, audit.translated, audit.references),
          model != nil,
          do: {resolver, f}

    assert Enum.any?(selected, &(elem(&1, 0) == IndexModels))
    assert Enum.any?(selected, &(elem(&1, 0) == FileModels))

    for {resolver, function} <- selected do
      for altered <- [
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "inputs"], []),
            put_in(function, ["signature", "abi"], "C")
          ] do
        assert is_nil(resolver.resolve(altered, audit.translated, audit.references))
      end

      if resolver == IndexModels do
        impl = function["src"]["TraitImpl"]["impl_ref"]["id"]

        changed =
          Map.update!(audit.translated, "trait_impls", fn implementations ->
            Enum.map(implementations, fn
              %{"def_id" => ^impl} = item -> Map.put(item, "methods", [])
              other -> other
            end)
          end)

        assert is_nil(IndexModels.resolve(function, changed, audit.references))
      end
    end

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "parser.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom parserTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(property, original)
    source = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(source)

    for broken <- [
          String.replace(rust, "u16::from_le_bytes", "u16::from_be_bytes"),
          String.replace(rust, "Ok(0) => Ok(None)", "Ok(0) => Ok(Some(0))")
        ] do
      refute broken == rust
      File.write!(source, broken)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      assert error.message =~ "Read/ReadProperties.lean:"
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
