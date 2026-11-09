defmodule Lynx.Rust.FileOpenOptionsTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  alias Lynx.Rust.{CallModels, DropModels, FileOpenModels, Project, Proofs}
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for writable reopen proofs")

  @tag :tmp_dir
  test "verifies the actual builder, cross-crate writable reopen and owned append", %{
    tmp_dir: tmp
  } do
    {workspace, project, fixture} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, ["OpenOptionsProperties"])

    properties =
      Enum.map(
        ~w(core_mode composition caller_checked caller_every_run recovery_checked recovery_every_run failure_checked failure_every_run),
        &("Record.OpenOptionsProperties." <> &1)
      )

    options =
      fixture
      |> Keyword.drop([:roots, :proof_modules])
      |> Keyword.merge(
        roots: [
          "io_protocol::open_readwrite",
          "io_protocol::reopen_then_append",
          "io_protocol::reopen_then_recover"
        ],
        owned_drops: true,
        proof_modules: ["Record.OpenOptionsProperties"],
        required_properties: properties
      )

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn evidence ->
             Map.get(evidence, :theorem) == "Record.OpenOptionsProperties.composition" and
               "Record.OpenOptionsProperties.core_mode" in evidence.contracts_used
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    audit = result.extraction.audit

    parser =
      Enum.find(audit.functions, fn function ->
        List.last(function["item_meta"]["name"]) == %{"Ident" => ["recover_log", 0]}
      end)

    [drop | _] = structural_drops(parser["body"])
    assert DropModels.nonpanicking_site?(drop, parser, audit.translated, audit.references)

    refute DropModels.nonpanicking_site?(
             put_in(drop, ["fn_ptr", "kind", "Fun"], -1),
             parser,
             audit.translated,
             audit.references
           )

    builders =
      for {_, %{native_open_options_type: _} = model} <- audit.external_calls, do: model

    assert length(builders) == 4

    for model <- builders do
      assert nil ==
               FileOpenModels.resolve(
                 put_in(model.function, ["signature", "is_unsafe"], true),
                 audit.translated,
                 audit.references
               )

      changed =
        Map.update!(audit.translated, "type_decls", fn types ->
          Enum.map(types, fn
            %{"def_id" => id} = type when id == model.native_open_options_type ->
              Map.put(type, "needs_drop", true)

            type ->
              type
          end)
        end)

      assert nil == FileOpenModels.resolve(model.function, changed, audit.references)

      if String.ends_with?(model.rust_name, "::read") or
           String.ends_with?(model.rust_name, "::write") do
        signature = CallModels.expand(model.function["signature"], audit.references)
        %{"Ref" => [region, type, "Mut"]} = signature["output"]
        changed = Map.put(signature, "output", %{"Ref" => [region, type, "Shared"]})

        assert nil ==
                 FileOpenModels.resolve(
                   Map.put(model.function, "signature", changed),
                   audit.translated,
                   audit.references
                 )
      end
    end

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "writable-reopen.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    vector = Path.join(project, "Record/Extraction/VectorModel.lean")
    vector_source = File.read!(vector)

    wrong_cutoff =
      String.replace(vector_source, "else RustM.fail .undef", "else RustM.fail .panic")

    refute wrong_cutoff == vector_source
    File.write!(vector, wrong_cutoff)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(vector, vector_source)
    Project.build!(project, options[:proof_modules])

    protocol = Path.join(workspace, "protocol/src/lib.rs")
    protocol_source = File.read!(protocol)
    wrong_record = String.replace(protocol_source, "values.push(value)", "values.push(0)")
    refute wrong_record == protocol_source
    File.write!(protocol, wrong_record)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "OpenOptionsProperties.lean:"
    File.write!(protocol, protocol_source)

    source = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(source)
    changed = String.replace(original, ".write(true)", ".write(false)")
    refute changed == original
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "OpenOptionsProperties.lean:"

    for flag <- ~w(append truncate create create_new) do
      File.write!(source, String.replace(original, ".write(true)", ".write(true).#{flag}(true)"))

      error =
        assert_raise CompileError, fn ->
          Lynx.Rust.verify!(workspace, "io-protocol", options)
        end

      assert error.description =~ "unverified external Rust call"
      assert error.description =~ flag
    end

    incoming = """
    pub struct OptionsContainer { pub options: std::fs::OpenOptions }
    pub fn incoming_options(options: &std::fs::OpenOptions, path: &str) -> io::Result<File> {
        options.open(path)
    }
    pub fn incoming_nested(container: &OptionsContainer, path: &str) -> io::Result<File> {
        container.options.open(path)
    }
    """

    File.write!(source, original <> incoming)

    for root <- ~w(io_core::incoming_options io_core::incoming_nested) do
      error =
        assert_raise CompileError, fn ->
          Lynx.Rust.verify!(
            workspace,
            "io-protocol",
            Keyword.update!(options, :roots, &(&1 ++ [root]))
          )
        end

      assert error.description =~ "OpenOptions must be constructed locally"
    end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end

  defp structural_drops(%{"Drop" => drop}), do: [drop]

  defp structural_drops(node) when is_map(node),
    do: Enum.flat_map(Map.values(node), &structural_drops/1)

  defp structural_drops(node) when is_list(node), do: Enum.flat_map(node, &structural_drops/1)
  defp structural_drops(_), do: []
end
