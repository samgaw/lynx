defmodule Lynx.Rust.OwnedStringTest do
  use ExUnit.Case
  alias Lynx.Rust.{OwnedStringModels, Project, Proofs}
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/OwnedTextProperties.lean", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for owned UTF-8 text proofs")

  @tag :tmp_dir
  test "proves owned text byte recovery and cross-crate composition", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for item <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@workspace, item), Path.join(workspace, item))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "OwnedText"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.join(@workspace, "proofs/.lake/packages"),
      Path.join(project, ".lake/packages")
    )

    property = Path.join(project, "OwnedText/Properties.lean")
    original = File.read!(@proof)
    File.write!(property, original)

    required =
      Enum.map(
        ~w(roundtrip composition decode_invalid invalid_bytes non_ascii append_unicode append_spec),
        &("OwnedText.Properties." <> &1)
      )

    options = [
      tools: @tools,
      roots:
        ~w(experiment_analysis::decode_owned experiment_analysis::append_owned experiment_analysis::owned_bytes_roundtrip),
      mir: :elaborated,
      lean_project: project,
      module_prefix: "OwnedText.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["OwnedText.Properties"],
      required_properties: required
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    refute Enum.any?(
             result.verification.guarantees,
             &(Map.get(&1, :theorem) == "OwnedText.Properties.append_cutoff")
           )

    audit = result.extraction.audit

    for {id, model} <- audit.external_calls, model[:owned_string_op] do
      function = Enum.find(audit.external_functions, &(&1["def_id"] == id))
      assert function

      for changed <- [
            put_in(function, ["signature", "abi"], "C"),
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "is_variadic"], true),
            put_in(function, ["signature", "output"], %{"Scalar" => "Bool"}),
            put_in(function, ["generics", "outlives"], ["unproved"])
          ] do
        refute OwnedStringModels.resolve(changed, audit.translated, audit.references)
      end
    end

    file = Proofs.file!(result.extraction, options[:proof_modules], required_properties: required)
    export = Path.join(tmp, "owned-text.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    model = Path.join(project, "OwnedText/Extraction/OwnedStringModel.lean")
    model_source = File.read!(model)
    assert "OwnedText.Extraction.OwnedStringModel" in result.extraction.audit_modules

    for {path, source} <- [{property, original}, {model, model_source}],
        extra <- [
          "private axiom hidden_owned : False",
          "private theorem unfinished_owned : True := by sorry"
        ] do
      File.write!(path, source <> "\n" <> extra <> "\n")
      Project.build!(project, ["OwnedText.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(path, source)
      Project.build!(project, ["OwnedText.Properties"])
    end

    for {path, before, replacement} <- [
          {property, "= .ok input := by", "= .ok ⟨Slice.from [] (by simp)⟩ := by"},
          {property, "OwnedString.pushStr text view = RustM.fail .undef",
           "OwnedString.pushStr text view = RustM.ok (text ++ suffix)"},
          {Path.join(workspace, "core/src/protocol.rs"), "Err(error) => Err(error.into_bytes()),",
           "Err(error) => Err(crate::collections::replace_first(error.into_bytes(), 0).1),"},
          {Path.join(workspace, "analysis/src/lib.rs"),
           "experiment_core::protocol::owned_bytes_roundtrip(bytes)",
           "experiment_core::collections::replace_first(experiment_core::protocol::owned_bytes_roundtrip(bytes), 0).1"}
        ] do
      source = File.read!(path)
      changed = String.replace(source, before, replacement)
      refute changed == source
      File.write!(path, changed)

      assert_raise RuntimeError, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

      File.write!(path, source)
    end

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports
  end
end
