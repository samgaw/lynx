defmodule Lynx.Rust.FileResourceTest do
  use ExUnit.Case
  alias Lynx.Rust.{NativeOwnedDrops, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "+owned-drops-v1"),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-drops backend")

  @tag :tmp_dir
  test "file resources retain shared ownership and close only on final destruction", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "FileResource"))

    for {source, target} <- [
          {"NativeFileResourceModel.lean", "Model"},
          {"NativeFileResource.lean", "Properties"}
        ],
        do:
          File.cp!(Path.join(@fixture, source), Path.join(project, "FileResource/#{target}.lean"))

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      Enum.map(
        ~w(cleanup_contract cleanup_ready construct_next final_release_next clone_next retained_release_next retained_final_release_next complete_cycle sync_contract unregistered_cleanup sync_ready_next cycle_keeps_disk),
        &("FileResource.Properties." <> &1)
      )

    options = [
      roots: ["effects_native::file_resource_cycle", "effects_native::file_resource_sync"],
      cargo: [features: ["file-resource-handles"]],
      files: :regular,
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "FileResource.Extraction",
      proof_modules: ["FileResource.Model", "FileResource.Properties"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert [%{lean_name: "effects_native.FileResource.drop_owned"}] =
             result.verification.resource_cleanup

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "FileResource.Properties.sync_ready_next")
           )

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "physical descriptor reclamation")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    check_cleanup_identity!(result.extraction.audit)

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "file-resource.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for module <- ~w(Model Properties) do
      path = Path.join(project, "FileResource/#{module}.lean")
      source = File.read!(path)

      for extra <- [
            "private axiom fileResourceTrust : False",
            "private theorem unfinishedResource : True := by sorry"
          ] do
        File.write!(path, source <> "\n" <> extra <> "\n")
        Project.build!(project, options[:proof_modules])
        assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
        File.write!(path, source)
      end
    end

    property = Path.join(project, "FileResource/Properties.lean")
    original = File.read!(property)

    for {correct, wrong} <- [
          {"next () (retained env state)", "next () (retired env state 4)"},
          {"some ⟨⟨#[1]⟩, 4⟩", "some ⟨⟨#[2]⟩, 4⟩"}
        ] do
      changed = String.replace(original, correct, wrong)
      refute changed == original
      File.write!(property, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Project.build!(project, options[:proof_modules])
      end

      File.write!(property, original)
    end

    core = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(core)

    changed =
      String.replace(
        rust,
        "    file.sync_all()",
        "    match file.sync_all() {\n        Ok(()) => file.sync_all(),\n        Err(error) => Err(error),\n    }"
      )

    refute changed == rust
    File.write!(core, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "effects-native", options)
      end

    assert error.message =~ "FileResource/Properties.lean:"
    File.write!(core, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports

    assert_raise CompileError, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", Keyword.delete(options, :files))
    end

    assert_raise CompileError, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", Keyword.delete(options, :owned_drops))
    end
  end

  defp check_cleanup_identity!(audit) do
    t = audit.translated

    type =
      Enum.find(
        t["type_decls"],
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["FileResource", 0]})
      )

    payload = %{
      "Adt" => %{
        "id" => type["def_id"],
        "builtin" => nil,
        "generics" => Lynx.Rust.ResourceModels.args([])
      }
    }

    destructor = NativeOwnedDrops.function_for(payload, t, audit.references)
    assert destructor

    for changed <- [
          put_in(t, ["options", "owned_drops"], false),
          update_in(t, ["fun_decls"], &(&1 ++ [destructor])),
          update_in(t, ["fun_decls"], fn fs ->
            Enum.map(fs, fn f ->
              if f == destructor,
                do:
                  put_in(f, ["body", "Structured", "body", "statements"], [
                    %{"kind" => %{"Panic" => %{}}}
                  ]),
                else: f
            end)
          end)
        ] do
      refute NativeOwnedDrops.function_for(payload, changed, audit.references)
    end
  end
end
