defmodule Lynx.Rust.FileCreateTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned patched backend")

  @tag :tmp_dir
  test "exclusive creation preserves existing files and does not invent directory durability", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Create"))
    property = Path.join(project, "Create/Properties.lean")
    File.cp!(Path.join(@fixture, "CreateProperties.lean"), property)
    original = File.read!(property)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      Enum.map(
        ~w(create_next not_directory_synced existing_success_exhausts existing_error write_created_next namespace_bound),
        &("Create.Properties." <> &1)
      )

    options = [
      roots: ["io_protocol::create_fresh", "io_core::write_once"],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      module_prefix: "Create.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Create.Properties"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    {_, constructor} =
      Enum.find(result.extraction.audit.external_calls, fn {_, model} ->
        String.ends_with?(model.rust_name, "::create_new")
      end)

    original_function = constructor.function
    audit = result.extraction.audit

    for changed <- [
          put_in(original_function, ["signature", "is_unsafe"], true),
          put_in(original_function, ["signature", "inputs"], []),
          put_in(original_function, ["item_meta", "name", Access.at(3)], %{
            "Ident" => ["create", 0]
          })
        ] do
      assert is_nil(Lynx.Rust.FileOpenModels.resolve(changed, audit.translated, audit.references))
    end

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.contains?(&1.rust_name, "create_new")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "create.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom createTrust : False",
          "private theorem unfinishedCreate : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    wrong = String.replace(original, "= some [] := by", "= some names := by")
    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)
    source = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(source)
    changed = String.replace(rust, "File::create_new(path)", "File::open(path)")
    refute changed == rust
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Create/Properties.lean:"
    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
