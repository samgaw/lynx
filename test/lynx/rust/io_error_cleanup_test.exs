defmodule Lynx.Rust.IoErrorCleanupTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned patched backend")

  @tag :tmp_dir
  test "consumes admitted OS errors and composes actual publication acknowledgement", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Publish"))

    File.cp!(
      Path.join(@fixture, "PublishProperties.lean"),
      Path.join(project, "Publish/Properties.lean")
    )

    File.cp!(
      Path.join(@fixture, "NamedRecovery.lean"),
      Path.join(project, "Publish/NamedRecovery.lean")
    )

    File.cp!(
      Path.join(@fixture, "PayloadProperties.lean"),
      Path.join(project, "Publish/Payload.lean")
    )

    File.cp!(
      Path.join(@fixture, "WordRecovery.lean"),
      Path.join(project, "Publish/WordRecovery.lean")
    )

    File.cp!(
      Path.join(@fixture, "CommitProperties.lean"),
      Path.join(project, "Publish/Commit.lean")
    )

    property = Path.join(project, "Publish/IoErrors.lean")
    File.cp!(Path.join(@fixture, "IoErrorProperties.lean"), property)

    File.cp!(
      Path.join(@fixture, "FramedCommitProperties.lean"),
      Path.join(project, "Publish/Framed.lean")
    )

    original = File.read!(property)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      Enum.map(
        ~w(explicit_cleanup implicit_cleanup missing_cleanup custom_cleanup duplicate_cleanup repeated_cleanup commit_ready acknowledged rejected_ack),
        &("Publish.IoErrors." <> &1)
      )

    properties =
      properties ++
        ~w(Publish.Commit.Framed.commit_shared Publish.Commit.Framed.acknowledged_prefix)

    options = [
      roots: [
        "io_protocol::commit_ack",
        "io_core::discard_io_error_implicit",
        "io_protocol::publish_file",
        "io_protocol::recover_named_word",
        "io_protocol::open_readonly",
        "io_protocol::sync_directory",
        "io_core::synchronize"
      ],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      module_prefix: "Publish.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: [
        "Publish.Properties",
        "Publish.Payload",
        "Publish.NamedRecovery",
        "Publish.WordRecovery",
        "Publish.Commit",
        "Publish.IoErrors",
        "Publish.Framed"
      ],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.contains?(&1.rust_name, "sync_all")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "io-error.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom ioErrorTrust : False",
          "private theorem unfinishedIoError : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    wrong =
      String.replace(
        original,
        "(.ok false,disposed)",
        "(.ok true,disposed)"
      )

    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)

    source = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(source)

    changed =
      String.replace(
        rust,
        "pub fn discard_io_error(error: io::Error) {\n    drop(error);\n}",
        "pub fn discard_io_error(error: io::Error) {\n    drop(error);\n    panic!();\n}"
      )

    refute changed == rust
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Publish/IoErrors.lean:"
    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
    check_destructor_identity!(result.extraction.llbc)

    protocol = Path.join(workspace, "protocol/src/lib.rs")

    File.write!(
      protocol,
      File.read!(protocol) <>
        "\npub fn discard_custom_io_error() { io_core::discard_io_error(std::io::Error::other(\"custom\")); }\n"
    )

    custom = Keyword.update!(options, :roots, &["io_protocol::discard_custom_io_error" | &1])
    assert_raise CompileError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", custom) end

    assert_raise CompileError, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", Keyword.delete(options, :files))
    end
  end

  defp check_destructor_identity!(path) do
    document = JSON.decode!(File.read!(path))
    refs = Lynx.Rust.LLBC.type_references!(document)
    translated = Lynx.Rust.CallModels.expand(document["translated"], refs)

    function =
      Enum.find(translated["fun_decls"], fn f ->
        f && List.last(f["item_meta"]["name"]) == %{"Ident" => ["discard_io_error_implicit", 0]}
      end)

    drop = find_drop(function["body"])

    assert {:ok, %{native_kind: :io_error, function: fid, impl: iid}} =
             Lynx.Rust.NativeDrops.site(drop, translated, %{})

    cleanup = Enum.find(translated["fun_decls"], &(&1 && &1["def_id"] == fid))
    implementation = Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == iid))
    error = Lynx.Rust.FileModels.error_declaration(translated)

    for {key, item} <- [
          {"fun_decls", put_in(cleanup, ["signature", "is_unsafe"], false)},
          {"fun_decls", put_in(cleanup, ["item_meta", "name"], [])},
          {"trait_impls", Map.put(implementation, "src", "Normal")},
          {"trait_impls", Map.put(implementation, "methods", [])},
          {"type_decls", Map.put(error, "needs_drop", false)},
          {"type_decls", put_in(error, ["item_meta", "name"], [])}
        ] do
      changed =
        Map.update!(translated, key, fn items ->
          Enum.map(items, fn previous ->
            if previous && previous["def_id"] == item["def_id"], do: item, else: previous
          end)
        end)

      refute match?({:ok, _}, Lynx.Rust.NativeDrops.site(drop, changed, %{}))
    end
  end

  defp find_drop(%{"Drop" => drop}), do: drop
  defp find_drop(map) when is_map(map), do: Enum.find_value(Map.values(map), &find_drop/1)
  defp find_drop(list) when is_list(list), do: Enum.find_value(list, &find_drop/1)
  defp find_drop(_), do: nil
end
