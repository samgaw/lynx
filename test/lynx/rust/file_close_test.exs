defmodule Lynx.Rust.FileCloseTest do
  use ExUnit.Case
  alias Lynx.Rust.{CallModels, FileDrops, LLBC, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "owned files close through actual Rust destruction without losing their disk images", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Close"))
    property = Path.join(project, "Close/Properties.lean")
    original = File.read!(Path.join(@fixture, "CloseProperties.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      Enum.map(
        ~w(explicit_close implicit_close_contract synchronize_close close_is_not_sync failed_close_consumes close_lifecycle),
        &("Close.Properties." <> &1)
      )

    options = [
      roots: [
        "io_protocol::consume_file",
        "io_protocol::implicit_close",
        "io_protocol::synchronize_then_close"
      ],
      execution: :runtime,
      files: :regular,
      tools: @tools,
      lean_project: project,
      module_prefix: "Close.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Close.Properties"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Close.Properties.synchronize_close")
           )

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "physical descriptor reclamation")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    check_destructor_identity!(result.extraction.llbc)

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "close.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom trustClose : False",
          "private theorem unfinishedClose : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(property, original)
    end

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
    protocol = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(protocol)

    for {changed, exception} <- [
          {String.replace(rust, "    drop(file);", "    drop(file);\n    panic!();",
             global: false
           ), RuntimeError},
          {String.replace(rust, "    drop(file);", "    std::mem::forget(file);", global: false),
           CompileError}
        ] do
      refute changed == rust
      File.write!(protocol, changed)

      error =
        assert_raise exception, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      if exception == RuntimeError do
        assert error.message =~ "native Lean project command failed"
        assert error.message =~ "Close/Properties.lean:"
      else
        assert error.description =~
                 ~r/unverified external Rust call core::mem::forget|structural drop erasure rejected/

        assert error.file =~ "protocol/src/lib.rs"
      end

      File.write!(protocol, rust)
    end

    before_close =
      String.replace(rust, "    drop(file);", "    panic!();\n    drop(file);", global: false)

    File.write!(protocol, before_close)

    error =
      assert_raise CompileError, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.description =~ ~r/native owner lifetime|structural drop erasure rejected|unwind/
    assert error.file =~ "protocol/src/lib.rs"
    File.write!(protocol, rust)

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    assert_raise CompileError, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", Keyword.delete(options, :files))
    end

    # A file-only extraction must not require an unrelated std::io::Error type.
    standalone =
      Regex.replace(
        ~r/\/-- The actual cross-crate Rust caller.*?(?=\/-- Closing an unsynchronized)/s,
        original,
        ""
      )

    refute standalone == original
    File.write!(property, standalone)

    isolated =
      options
      |> Keyword.put(:roots, ["io_protocol::consume_file", "io_protocol::implicit_close"])
      |> Keyword.put(:required_properties, properties -- ["Close.Properties.synchronize_close"])

    result = Lynx.Rust.verify!(workspace, "io-protocol", isolated)
    assert [%{status: :ok}] = result.reports
    assert [%{rust: "std::fs::File"}] = result.extraction.external_types
  end

  defp check_destructor_identity!(path) do
    document = JSON.decode!(File.read!(path))
    refs = LLBC.type_references!(document)
    translated = CallModels.expand(document["translated"], refs)
    drop = find_drop(translated["fun_decls"])
    assert drop
    assert {:ok, %{function: fid, impl: iid}} = FileDrops.site(drop, translated, %{})
    function = Enum.find(translated["fun_decls"], &(&1 && &1["def_id"] == fid))
    implementation = Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == iid))

    for changed <- [
          put_in(function, ["signature", "is_unsafe"], false),
          put_in(function, ["src", "TraitImpl", "reuses_default"], true),
          put_in(function, ["item_meta", "name"], []),
          put_in(function, ["generics", "regions"], [%{"index" => 1}])
        ] do
      t = replace_item(translated, "fun_decls", fid, changed)
      assert {:error, _} = FileDrops.site(drop, t, %{})
    end

    for changed <- [
          Map.put(implementation, "src", "Normal"),
          Map.put(implementation, "is_unsafe", true),
          Map.put(implementation, "methods", []),
          put_in(implementation, ["impl_trait", "id"], -1)
        ] do
      t = replace_item(translated, "trait_impls", iid, changed)
      assert {:error, _} = FileDrops.site(drop, t, %{})
    end
  end

  defp replace_item(translated, key, id, value),
    do:
      Map.update!(
        translated,
        key,
        &Enum.map(&1, fn item ->
          if item && item["def_id"] == id, do: value, else: item
        end)
      )

  defp find_drop(%{"Drop" => drop}), do: drop
  defp find_drop(map) when is_map(map), do: Enum.find_value(Map.values(map), &find_drop/1)
  defp find_drop(list) when is_list(list), do: Enum.find_value(list, &find_drop/1)
  defp find_drop(_), do: nil
end
