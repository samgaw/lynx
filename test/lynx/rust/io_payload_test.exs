defmodule Lynx.Rust.IoPayloadTest do
  use ExUnit.Case
  alias Lynx.Rust.{IoErrorModels, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do:
      @moduletag(
        skip: "set LYNX_AENEAS_DIR to runtime tools and LYNX_FULL_MIR=1 for IO payload proofs"
      )

  @tag :tmp_dir
  test "classifies actual IO errors, preserves borrowed state and consumes owning errors and files",
       %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "IoPayload"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    property = Path.join(project, "IoPayload/Properties.lean")
    original = File.read!(Path.join(@fixture, "IoPayloadProperties.lean"))
    File.write!(property, original)

    required =
      Enum.map(
        ~w(core_spec borrowed_kind classified read_contract open_error read_error read_success scenarios every_run rejected),
        &("IoPayload.Properties." <> &1)
      )

    options = [
      tools: @tools,
      sysroot: :full_mir,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      roots: ~w(io_protocol::error_is_retryable io_protocol::read_is_retryable),
      lean_project: project,
      module_prefix: "IoPayload.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["IoPayload.Properties"],
      required_properties: required
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert Enum.any?(result.verification.unverified_external_calls, fn call ->
             call.rust_name =~ "::kind" and call.implementation_verified == false
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    audit = result.extraction.audit
    [{id, _}] = Enum.filter(audit.external_calls, fn {_, model} -> model[:io_error_kind_type] end)
    function = Enum.find(audit.translated["fun_decls"], &(&1 && &1["def_id"] == id))

    for altered <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "inputs"], []),
          put_in(function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(function, ["generics", "regions", Access.at(0), "index"], 9)
        ] do
      refute IoErrorModels.resolve(altered, audit.translated, audit.references)
    end

    kind = audit.external_calls[id].io_error_kind_type

    for changed_kind <- [
          "Opaque",
          %{"Enum" => [%{"id" => 0, "name" => "Payload", "fields" => [%{"ty" => "Never"}]}]}
        ] do
      changed =
        Map.update!(audit.translated, "type_decls", fn types ->
          Enum.map(types, fn
            %{"def_id" => ^kind} = type -> Map.put(type, "kind", changed_kind)
            other -> other
          end)
        end)

      refute IoErrorModels.resolve(function, changed, audit.references)
    end

    file = Proofs.file!(result.extraction, options[:proof_modules], required_properties: required)
    export = Path.join(tmp, "payload.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    model = Path.join(project, "IoPayload/Extraction/IoErrorModel.lean")
    model_source = File.read!(model)
    assert "IoPayload.Extraction.IoErrorModel" in result.extraction.audit_modules

    for {path, source} <- [{property, original}, {model, model_source}],
        extra <- [
          "private axiom hidden_payload : False",
          "private theorem unfinished_payload : True := by sorry"
        ] do
      File.write!(path, source <> "\n" <> extra <> "\n")
      Project.build!(project, ["IoPayload.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(path, source)
      Project.build!(project, ["IoPayload.Properties"])
    end

    for {relative, before, replacement} <- [
          {"core/src/lib.rs", "kind == io::ErrorKind::Interrupted",
           "kind == io::ErrorKind::NotFound"},
          {"protocol/src/lib.rs", "    drop(file);\n    retryable", "    drop(file);\n    false"},
          {"protocol/src/lib.rs", "            drop(error);\n            retryable",
           "            drop(error);\n            !retryable"}
        ] do
      path = Path.join(workspace, relative)
      source = File.read!(path)
      changed = String.replace(source, before, replacement)
      refute changed == source
      File.write!(path, changed)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      assert error.message =~ "IoPayload/Properties.lean:"
      refute error.message =~ "Unknown identifier"
      File.write!(path, source)
    end

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
