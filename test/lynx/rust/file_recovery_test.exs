defmodule Lynx.Rust.FileRecoveryTest do
  use ExUnit.Case
  alias Lynx.Rust.{FileModels, Project, Proofs}
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
  test "composes actual write acknowledgement, crash images and recovery", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Recovery"))

    File.write!(
      Path.join(project, "Recovery/Properties.lean"),
      File.read!(Path.join(@fixture, "Properties.lean")) |> String.replace("Disk", "Recovery")
    )

    File.write!(
      Path.join(project, "Recovery/ReadProperties.lean"),
      File.read!(Path.join(@fixture, "ReadProperties.lean"))
      |> String.replace("Read.Properties", "Recovery.Properties")
      |> String.replace("Read.ReadProperties", "Recovery.ReadProperties")
    )

    property = Path.join(project, "Recovery/RecoveryProperties.lean")
    original = File.read!(Path.join(@fixture, "RecoveryProperties.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: [
        "io_protocol::recover_word",
        "io_protocol::read_word",
        "io_protocol::write_then_sync"
      ],
      execution: :runtime,
      files: :regular,
      tools: @tools,
      lean_project: project,
      module_prefix: "Recovery.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: [
        "Recovery.Properties",
        "Recovery.ReadProperties",
        "Recovery.RecoveryProperties"
      ],
      required_properties:
        Enum.map(
          ~w(seek_from_contract seek_next recover_success acknowledged_image acknowledged_recovery restart_recovery restart_recovery_default recover_seek_error recovery_image_idempotent word_acknowledged_recovery),
          &("Recovery.RecoveryProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports
    assert "Recovery.Extraction.FileModel" in result.extraction.model_modules

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Recovery.RecoveryProperties.acknowledged_recovery")
           )

    assert Enum.any?(result.verification.external_models, &String.contains?(&1, "host admission"))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    audit = result.extraction.audit

    {id, %{file_seek_type: seek_type}} =
      Enum.find(audit.external_calls, fn {_, m} -> m[:file_seek_type] != nil end)

    function = Enum.find(audit.external_functions, &(&1["def_id"] == id))

    assert %{file_seek_type: ^seek_type} =
             FileModels.resolve(function, audit.translated, audit.references)

    for change <- [:opaque, :reordered, :unsigned_offset] do
      changed =
        Map.update!(audit.translated, "type_decls", fn types ->
          Enum.map(types, fn
            %{"def_id" => ^seek_type} = type ->
              case change do
                :opaque ->
                  Map.put(type, "kind", "Opaque")

                :reordered ->
                  update_in(type, ["kind", "Enum"], &Enum.reverse/1)

                :unsigned_offset ->
                  update_in(type, ["kind", "Enum"], fn variants ->
                    List.update_at(
                      variants,
                      2,
                      &put_in(&1, ["fields", Access.at(0), "ty"], %{
                        "Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}
                      })
                    )
                  end)
              end

            other ->
              other
          end)
        end)

      assert is_nil(FileModels.resolve(function, changed, audit.references))
    end

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "recovery.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    generated = Path.join(project, "Recovery/Extraction/FileModel.lean")
    model_source = File.read!(generated)

    for {target, source} <- [{property, original}, {generated, model_source}],
        extra <- [
          "private axiom recoveryTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(target, source <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(target, source)
    end

    wrong_adapter =
      String.replace(
        model_source,
        ".Start offset => .start offset",
        ".Start offset => .start 1#u64"
      )

    refute wrong_adapter == model_source
    File.write!(generated, wrong_adapter)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Project.build!(project, options[:proof_modules])
      end

    assert error.message =~ "Recovery/RecoveryProperties.lean:"
    File.write!(generated, model_source)

    source = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(source)
    broken = String.replace(rust, "io_core::seek_to(file, 0)", "io_core::seek_to(file, 1)")
    refute broken == rust
    File.write!(source, broken)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Recovery/RecoveryProperties.lean:"
    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
