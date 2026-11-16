defmodule Lynx.Rust.ExactReadTest do
  use ExUnit.Case
  alias Lynx.Rust.{ArrayModels, ExactRead, IoErrorModels, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do:
      @moduletag(skip: "set LYNX_AENEAS_DIR to runtime tools and LYNX_FULL_MIR=1 for exact reads")

  @tag :tmp_dir
  test "proves actual standard exact reads across workspace crates and rejects invalid proofs", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "ExactRead"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    property = Path.join(project, "ExactRead/Properties.lean")
    original = File.read!(Path.join(@fixture, "ExactReadProperties.lean"))
    File.write!(property, original)

    required =
      Enum.map(
        ~w(empty_input eof_contract eof_input partial_eof complete_read interrupted_retry other_error complete_prefix word_complete caller_complete eof_prefix word_eof caller_eof fill_no_panic),
        &("ExactRead.Properties." <> &1)
      )

    options = [
      tools: @tools,
      sysroot: :full_mir,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      roots: ["io_protocol::optional_exact_word"],
      lean_project: project,
      module_prefix: "ExactRead.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["ExactRead.Properties"],
      required_properties: required
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    audit = result.extraction.audit
    helpers = Enum.filter(audit.functions, &ExactRead.selected?(&1, audit.translated))
    assert Enum.any?(helpers, &(inspect(&1["item_meta"]["name"]) =~ "default_read_exact"))

    for function <- helpers do
      refute ExactRead.selected?(
               put_in(function, ["signature", "is_unsafe"], true),
               audit.translated
             )
    end

    [{repeat_id, _}] =
      Enum.filter(audit.external_calls, fn {_, model} -> model[:byte_array_repeat] end)

    repeat_args = Enum.flat_map(audit.functions, &regular_arguments(&1["body"], repeat_id))
    assert repeat_args != []

    for args <- repeat_args do
      assert ArrayModels.repeat_call?(args, audit.translated, audit.references)

      for changed <- [
            Map.put(args, "types", [%{"Scalar" => "Bool"}]),
            Map.put(args, "trait_refs", []),
            Map.put(args, "regions", ["Erased"])
          ] do
        refute ArrayModels.repeat_call?(changed, audit.translated, audit.references)
      end
    end

    for {id, model} <- audit.external_calls, model[:io_error_operation] do
      function = Enum.find(audit.external_functions, &(&1["def_id"] == id))
      assert function

      for changed <- [
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "is_variadic"], true),
            put_in(function, ["signature", "abi"], "C")
          ] do
        refute IoErrorModels.resolve(changed, audit.translated, audit.references)
      end
    end

    {read_id, _} =
      Enum.find(audit.external_calls, fn {_, m} -> m.lean == "Lynx.NativeFile.read" end)

    reader = Enum.find(audit.external_functions, &(&1["def_id"] == read_id))
    impl_id = get_in(reader, ["src", "TraitImpl", "impl_ref", "id"])

    changed =
      Map.update!(audit.translated, "trait_impls", fn implementations ->
        Enum.map(implementations, fn
          %{"def_id" => ^impl_id} = impl -> Map.put(impl, "methods", [])
          other -> other
        end)
      end)

    assert {:error, _, _} =
             ExactRead.audit(audit.functions, audit.external_calls, changed, audit.references)

    file = Proofs.file!(result.extraction, options[:proof_modules], required_properties: required)
    export = Path.join(tmp, "exact-read.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    model = Path.join(project, "ExactRead/Extraction/IoErrorModel.lean")
    model_source = File.read!(model)

    for {path, source} <- [{property, original}, {model, model_source}],
        extra <- [
          "private axiom hidden_exact : False",
          "private theorem unfinished_exact : True := by sorry"
        ] do
      File.write!(path, source <> "\n" <> extra <> "\n")
      Project.build!(project, ["ExactRead.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(path, source)
      Project.build!(project, ["ExactRead.Properties"])
    end

    incorrect =
      String.replace(
        original,
        "(.ok (.Err eofError,⟨1⟩,prefixBuffer)",
        "(.ok (.Ok (),⟨1⟩,prefixBuffer)"
      )

    refute incorrect == original
    File.write!(property, incorrect)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", options)
    end

    File.write!(property, original)

    for {relative, before, replacement} <- [
          {"core/src/lib.rs", "Ok(u16::from_le_bytes(bytes))", "Ok(u16::from_be_bytes(bytes))"},
          {"protocol/src/lib.rs", "Ok(value) => Ok(Some(value)),", "Ok(_value) => Ok(Some(0)),"}
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

      assert error.message =~ "ExactRead/Properties.lean:"
      refute error.message =~ "Unknown identifier"
      File.write!(path, source)
    end

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end

  defp regular_arguments(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}, id),
    do: [args]

  defp regular_arguments(node, id) when is_map(node), do: regular_arguments(Map.values(node), id)

  defp regular_arguments(nodes, id) when is_list(nodes),
    do: Enum.flat_map(nodes, &regular_arguments(&1, id))

  defp regular_arguments(_, _), do: []
end
