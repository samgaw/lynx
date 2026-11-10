defmodule Lynx.Rust.ResourceCreationTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RESOURCE_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RESOURCE_DIR for resource creation proofs")

  @tag :tmp_dir
  test "constructor panic composes with actual cross-crate computation and caller cleanup", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Created"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    property = Path.join(project, "Created/Properties.lean")
    proof = File.read!(Path.join(@fixture, "ResourceCreateProperties.lean"))
    File.write!(property, proof)

    opts = [
      roots: ["ownership_nif::create_checked_resource", "ownership_nif::create_with_mutex"],
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["resource-unwind"]],
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Created.Extraction",
      proof_modules: ["Created.Properties"],
      required_properties:
        Enum.map(
          ~w(mutate checked inner create create_registered create_unregistered cleanup_registered cleanup_unregistered),
          &("Created.Properties." <> &1)
        )
    ]

    verify = fn -> Lynx.Rust.verify!(workspace, "ownership-nif", opts) end
    result = verify.()
    assert [%{status: :ok}] = result.reports
    captures = Enum.flat_map(result.extraction.captured_unwind, & &1.external_captures)
    assert length(captures) == 2
    assert Enum.all?(captures, &(&1.source != &1.wrapper))

    [model] =
      for {_, model} <- result.extraction.audit.external_calls,
          model[:native_captured_source],
          do: model

    assert model.native_cutoff_only
    assert model.resource_operation == "new"
    assert Enum.all?(captures, &(&1.source_name == model.native_captured_source_name))
    assert [%{status: :ok, cached: true}] = verify.().reports

    document = result.extraction.audit.document
    t = document["translated"]
    refs = Lynx.Rust.LLBC.type_references!(document)

    [helper] =
      Enum.filter(
        t["fun_decls"],
        &(&1 && hd(&1["item_meta"]["name"]) == %{"Ident" => ["LynxCompilerCapture", 0]})
      )

    source = Enum.at(t["fun_decls"], model.native_captured_source)

    for invalid <- [
          Map.put(helper, "body", %{}),
          Map.put(helper, "generics", %{}),
          Map.put(helper, "signature", source["signature"])
        ] do
      assert Lynx.Rust.NativePanicCapture.resolve(invalid, t, refs) == nil
    end

    missing = update_in(t, ["fun_decls"], &List.replace_at(&1, source["def_id"], nil))
    assert Lynx.Rust.NativePanicCapture.resolve(helper, missing, refs) == nil

    assert_raise ArgumentError, ~r/reserved compiler panic capture namespace/, fn ->
      Lynx.Rust.NativePanicCapture.prepare!(document)
    end

    before_capture =
      (Path.rootname(result.extraction.llbc) <> ".native-drops.llbc")
      |> File.read!()
      |> JSON.decode!()
      |> remove_constructor_exit(model.native_captured_source)

    assert_raise CompileError, ~r/missing its compiler unwind exit/, fn ->
      Lynx.Rust.LLBC.audit!(before_capture, result.extraction.audit.first_party,
        execution: :runtime,
        unwind: :captured,
        external_calls: [:captured_unwind_drops]
      )
    end

    file =
      Lynx.Rust.Proofs.file!(result.extraction, opts[:proof_modules],
        required_properties: opts[:required_properties]
      )

    export = Path.join(tmp, "resource-create.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom constructorTrust : False",
          "private theorem unfinishedConstructor : True := by sorry"
        ] do
      File.write!(property, proof <> "\n" <> extra)
      assert_raise RuntimeError, ~r/Rust properties or proof audit failed/, verify
    end

    wrong = String.replace(proof, "core.result.Result.Ok (!value)", "core.result.Result.Ok value")
    refute wrong == proof
    File.write!(property, wrong)
    assert_raise RuntimeError, ~r/native Lean project command failed/, verify
    File.write!(property, proof)
    source = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(source)
    File.write!(source, String.replace(original, "*value = !*value;", "*value = *value;"))
    assert_raise RuntimeError, ~r/native Lean project command failed/, verify
    File.write!(source, original)
    assert [%{status: :ok}] = verify.().reports
  end

  defp remove_constructor_exit(%{"kind" => %{"Call" => call}} = statement, source) do
    if get_in(call, ["call", "func", "Regular", "kind", "Fun"]) == source,
      do: put_in(statement, ["kind", "Call", "on_unwind", "statements"], []),
      else:
        Map.new(statement, fn {key, value} -> {key, remove_constructor_exit(value, source)} end)
  end

  defp remove_constructor_exit(map, source) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, remove_constructor_exit(value, source)} end)

  defp remove_constructor_exit(list, source) when is_list(list),
    do: Enum.map(list, &remove_constructor_exit(&1, source))

  defp remove_constructor_exit(value, _), do: value
end
