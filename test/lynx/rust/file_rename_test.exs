defmodule Lynx.Rust.FileRenameTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned patched backend")

  @tag :tmp_dir
  test "rename composes across crates and preserves open capabilities", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Rename"))
    property = Path.join(project, "Rename/Properties.lean")
    File.cp!(Path.join(@fixture, "RenameProperties.lean"), property)
    original = File.read!(property)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      Enum.map(
        ~w(replace_next successful_replace error_can_apply error_keeps_names replaced_capabilities same_inode_noop),
        &("Rename.Properties." <> &1)
      )

    options = [
      roots: ["io_protocol::rename_visible"],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      module_prefix: "Rename.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Rename.Properties"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    {rename_id, operation} =
      Enum.find(result.extraction.audit.external_calls, fn {_, model} ->
        String.ends_with?(model.rust_name, "std::fs::rename")
      end)

    original_function = operation.function
    audit = result.extraction.audit

    for index <- 0..1 do
      changed = Enum.map(audit.functions, &corrupt_dictionary(&1, rename_id, index))
      refute changed == audit.functions

      assert {:error, _, message} =
               Lynx.Rust.FileOpenModels.audit(
                 changed,
                 audit.external_calls,
                 audit.translated,
                 audit.references
               )

      assert message =~ "both paths"
    end

    for changed <- [
          put_in(original_function, ["signature", "is_unsafe"], true),
          put_in(original_function, ["signature", "inputs"], []),
          put_in(original_function, ["item_meta", "name", Access.at(2)], %{
            "Ident" => ["remove_file", 0]
          })
        ] do
      assert is_nil(Lynx.Rust.FileOpenModels.resolve(changed, audit.translated, audit.references))
    end

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.contains?(&1.rust_name, "std::fs::rename")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "rename.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom renameTrust : False",
          "private theorem unfinishedRename : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    wrong = String.replace(original, "lookup ⟨4⟩", "lookup ⟨3⟩")
    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)
    source = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(source)
    changed = String.replace(rust, "std::fs::rename(from, to)", "std::fs::rename(to, from)")
    refute changed == rust
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Rename/Properties.lean:"
    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end

  defp corrupt_dictionary(
         %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => g} = f},
         id,
         index
       ) do
    bad = %{"regions" => [], "outlives" => [], "skip_binder" => %{"Deduplicated" => -1}}
    %{"Regular" => %{f | "generics" => put_in(g, ["trait_refs", Access.at(index)], bad)}}
  end

  defp corrupt_dictionary(node, id, index) when is_map(node),
    do: Map.new(node, fn {key, value} -> {key, corrupt_dictionary(value, id, index)} end)

  defp corrupt_dictionary(node, id, index) when is_list(node),
    do: Enum.map(node, &corrupt_dictionary(&1, id, index))

  defp corrupt_dictionary(node, _, _), do: node
end
