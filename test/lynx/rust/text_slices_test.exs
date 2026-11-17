defmodule Lynx.Rust.TextSlicesTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @properties Path.expand("../../fixtures/rust_protocol/TextSlices.lean", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for borrowed text proofs")

  @tag :tmp_dir
  test "proves character-safe string slices across workspace crates", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for name <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@workspace, name), Path.join(workspace, name))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "TextSlices"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.join(@workspace, "proofs/.lake/packages"),
      Path.join(project, ".lake/packages")
    )

    path = Path.join(project, "TextSlices/Properties.lean")

    properties =
      File.read!(@properties)
      |> String.replace("__CALLER__", "experiment_analysis")
      |> String.replace("__CORE__", "experiment_analysis.experiment_core.protocol")

    File.write!(path, properties)

    required =
      Enum.map(
        ~w(window_composition window_valid split_roundtrip split_rejected windows_unicode window_utf8 split_utf8 checked_implementation checked_consistent checked_rejected checked_utf8 checked_unicode text_equal_bytes text_equal_reflexive text_prefix_bytes text_prefix_reflexive consume_implementation consume_by_values consume_exact consume_utf8),
        &("TextSlices.Properties." <> &1)
      )

    record = File.read!(Path.join(Path.dirname(@properties), "TextRecord.lean"))
    File.write!(Path.join(project, "TextSlices/Record.lean"), record)

    options = [
      tools: @tools,
      sysroot: :full_mir,
      mir: :promoted,
      lean_project: project,
      module_prefix: "TextSlices.Extraction",
      roots: [
        "experiment_analysis::text_window",
        "experiment_analysis::split_text",
        "experiment_analysis::checked_text_split",
        "experiment_analysis::text_equal",
        "experiment_analysis::text_has_prefix",
        "experiment_analysis::text_consume_prefix",
        "experiment_analysis::text_record"
      ],
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["TextSlices.Properties", "TextSlices.Record"],
      required_properties:
        required ++
          Enum.map(
            ~w(tagged_composition tagged_exact tagged_returns tagged_sound record_sound record_accepts record_rejects_first record_rejects_second record_total record_unicode),
            &("TextSlices.Record." <> &1)
          )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert Enum.all?(result.reports, &(&1.status == :ok))

    assert Enum.any?(result.extraction.translation["functions"], fn function ->
             function["def_id"] in result.extraction.audit.library_helpers and
               String.ends_with?(function["lean_name"], "core.str.Str.split_at_checked")
           end)

    refute Enum.any?(
             result.verification.unverified_external_calls,
             &String.ends_with?(&1.rust_name, "::split_at_checked")
           )

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok and &1.cached)
           )

    file =
      Lynx.Rust.Proofs.file!(result.extraction, ["TextSlices.Properties", "TextSlices.Record"])

    export = Path.join(tmp, "borrowed-text.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    model = Path.join(project, "TextSlices/Extraction/StringSlicesModel.lean")
    original_model = File.read!(model)

    bypassed =
      String.replace(
        original_model,
        "if TextSlices.Extraction.StringViews.isCharBoundary text range.start &&\n" <>
          "      TextSlices.Extraction.StringViews.isCharBoundary text range.end then",
        "if true then"
      )

    assert bypassed != original_model
    File.write!(model, bypassed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["TextSlices.Properties"])
    end

    File.write!(model, original_model)
    Lynx.Rust.Project.build!(project, ["TextSlices.Properties"])

    for extra <- [
          "private axiom hidden_dictionary : False",
          "private theorem unfinished_dictionary : True := by sorry"
        ] do
      File.write!(model, original_model <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["TextSlices.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(model, original_model)
      Lynx.Rust.Project.build!(project, ["TextSlices.Properties"])
    end

    for {relative, before, after_text} <- [
          {"core/src/protocol.rs", "text.get(start..end)", "text.get(0..end)"},
          {"core/src/protocol.rs", "text.split_at_checked(position)", "text.split_at_checked(0)"},
          {"core/src/protocol.rs", "left == right", "left != right"},
          {"core/src/protocol.rs", "text.starts_with(prefix)", "prefix.starts_with(text)"},
          {"core/src/protocol.rs", "text.strip_prefix(prefix)", "text.strip_prefix(\"\")"},
          {"analysis/src/lib.rs", "Some((name, value, remainder))",
           "Some((value, name, remainder))"},
          {"analysis/src/lib.rs", "Some((left, right))", "Some((right, left))"}
        ] do
      source = Path.join(workspace, relative)
      original = File.read!(source)
      changed = String.replace(original, before, after_text)
      assert changed != original
      File.write!(source, changed)

      assert_raise RuntimeError, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

      File.write!(source, original)
    end

    original = File.read!(path)

    File.write!(path, String.replace(original, "toStr \"é\"", "toStr \"x\""))

    assert_raise RuntimeError, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(path, original)

    for extra <- [
          "private axiom hidden_slice : False",
          "private theorem unfinished_slice : True := by sorry"
        ] do
      File.write!(path, original <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end
    end

    File.write!(path, original)

    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)

    File.write!(
      source,
      String.replace(original, "text.get(start..end)", "Some(&text[start..end])")
    )

    assert_raise CompileError, ~r/unverified external Rust call.*index/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(source, original)

    changed = String.replace(original, "text.starts_with(prefix)", "text.starts_with('a')")
    assert changed != original
    File.write!(source, changed)

    assert_raise CompileError, ~r/shared-str prefix/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(source, original)

    changed =
      String.replace(
        original,
        "text.strip_prefix(prefix)",
        "Some(unsafe { text.get_unchecked(prefix.len()..) })"
      )

    assert changed != original
    File.write!(source, changed)

    assert_raise CompileError, ~r/unchecked string borrowing is restricted/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(source, original)

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok)
           )
  end
end
