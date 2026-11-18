defmodule Lynx.Rust.PositionalIoTest do
  use ExUnit.Case
  alias Lynx.Rust.{FileModels, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the native runtime backend")

  @tag :tmp_dir
  test "checks positional writes, synchronized images and cursor-preserving reads", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Positional"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    File.write!(
      Path.join(project, "Positional/Base.lean"),
      File.read!(Path.join(@fixture, "Properties.lean"))
      |> String.replace("Disk", "Positional")
    )

    property = Path.join(project, "Positional/Properties.lean")
    original = File.read!(Path.join(@fixture, "PositionalProperties.lean"))
    File.write!(property, original)

    required =
      Enum.map(
        ~w(patch_order patch_persists_prefix patch_sync_error patch_write_error observe_contract observe_prefix observe_eof observe_error observe_outside),
        &("Positional.Proofs." <> &1)
      )

    modules = ["Positional.Base", "Positional.Properties"]

    options = [
      tools: @tools,
      roots: [
        "io_protocol::positional::patch",
        "io_protocol::positional::observe",
        "io_protocol::write_then_sync"
      ],
      execution: :runtime,
      files: :regular,
      lean_project: project,
      module_prefix: "Positional.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: modules,
      required_properties: required
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn
             %{kind: :cross_crate_contract, theorem: "Positional.Proofs.patch_persists_prefix"} ->
               true

             _ ->
               false
           end)

    audit = result.extraction.audit

    for operation <- ~w(readAt writeAt) do
      {id, model} =
        Enum.find(audit.external_calls, fn {_, model} ->
          model.lean == "Lynx.NativeFile." <> operation
        end)

      assert model.implementation_verified == false
      function = Enum.find(audit.external_functions, &(&1["def_id"] == id))

      other_slot = if operation == "readAt", do: 5, else: 0
      wrong_slot = put_in(function, ["src", "TraitImpl", "item_id"], other_slot)
      assert FileModels.resolve(wrong_slot, audit.translated, audit.references) == nil

      reused_default =
        put_in(function, ["src", "TraitImpl", "reuses_default"], true)

      assert FileModels.resolve(reused_default, audit.translated, audit.references) ==
               nil
    end

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file = Proofs.file!(result.extraction, modules, required_properties: required)
    export = Path.join(tmp, "positional.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom positionalTrust : False",
          "private theorem unfinishedPositional : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, modules)
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(property, original)
    source = Path.join(workspace, "protocol/src/positional.rs")
    rust = File.read!(source)

    wrong_offset =
      String.replace(rust, "write_at(file, bytes, offset)", "write_at(file, bytes, offset ^ 1)")

    refute wrong_offset == rust
    File.write!(source, wrong_offset)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Positional/Properties.lean:"
    File.write!(source, rust)
  end
end
