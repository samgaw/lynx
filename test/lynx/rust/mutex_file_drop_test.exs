defmodule Lynx.Rust.MutexFileDropTest do
  use ExUnit.Case
  alias Lynx.Rust.{CallModels, FileModels, LLBC, NativeDrops, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "+owned-drops-v1"),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-drops backend")

  @tag :tmp_dir
  test "composes owning mutex destruction with actual cross-crate file cleanup", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "MutexFile"))
    property = Path.join(project, "MutexFile/Properties.lean")
    original = File.read!(Path.join(@fixture, "MutexFileProperties.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      Enum.map(
        ~w(consuming implicit_consuming cycle no_implicit_sync poisoned_close_error crash_after_cleanup locked_rejected missing_close_choice),
        &("MutexFile.Properties." <> &1)
      )

    options = [
      roots: ["io_protocol::file_mutex_cycle", "io_protocol::implicit_file_mutex"],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      module_prefix: "MutexFile.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["MutexFile.Properties"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports
    assert [_ | _] = result.extraction.native_drops
    check_destructor_identity!(result.extraction.llbc)

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract && &1.theorem == "MutexFile.Properties.cycle")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "mutex-file.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom trustMutexFile : False",
          "private theorem unfinishedMutexFile : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(property, original)

    wrong =
      String.replace(
        original,
        "(.ok (), closed ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩)",
        "(.ok (), closed ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[2]⟩, 0, .nil⟩)"
      )

    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)

    core = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(core)

    changed =
      String.replace(
        rust,
        "    drop(mutex);",
        "    drop(mutex);\n    panic!();"
      )

    refute changed == rust
    File.write!(core, changed)

    error =
      assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end

    assert error.message =~ "native Lean project command failed"
    assert error.message =~ "MutexFile/Properties.lean:"
    File.write!(core, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    for disabled <- [Keyword.delete(options, :files), Keyword.delete(options, :owned_drops)] do
      assert_raise CompileError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", disabled) end
    end
  end

  defp check_destructor_identity!(path) do
    document = JSON.decode!(File.read!(path))
    refs = LLBC.type_references!(document)
    translated = CallModels.expand(document["translated"], refs)
    drop = find_drop(translated["fun_decls"])
    assert drop

    assert {:ok, %{native_kind: :mutex, function: fid, impl: iid}} =
             NativeDrops.site(drop, translated, %{})

    function = Enum.find(translated["fun_decls"], &(&1 && &1["def_id"] == fid))
    implementation = Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == iid))
    file = FileModels.declaration(translated)

    for {key, item} <- [
          {"fun_decls", put_in(function, ["signature", "is_unsafe"], false)},
          {"fun_decls", put_in(function, ["item_meta", "name"], [])},
          {"trait_impls", Map.put(implementation, "src", "Normal")},
          {"trait_impls", Map.put(implementation, "methods", [])},
          {"type_decls", Map.put(file, "needs_drop", false)},
          {"type_decls", put_in(file, ["item_meta", "name"], [])}
        ] do
      changed =
        Map.update!(translated, key, fn items ->
          Enum.map(items, fn previous ->
            if previous && previous["def_id"] == item["def_id"], do: item, else: previous
          end)
        end)

      assert {:error, _} = NativeDrops.site(drop, changed, %{})
    end

    assert {:error, _} =
             NativeDrops.site(drop, put_in(translated, ["options", "owned_drops"], false), %{})
  end

  defp find_drop(%{"Drop" => drop}), do: drop
  defp find_drop(map) when is_map(map), do: Enum.find_value(Map.values(map), &find_drop/1)
  defp find_drop(list) when is_list(list), do: Enum.find_value(list, &find_drop/1)
  defp find_drop(_), do: nil
end
