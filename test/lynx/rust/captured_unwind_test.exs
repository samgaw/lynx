defmodule Lynx.Rust.CapturedUnwindTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_CAPTURED_AENEAS_DIR for captured unwind proofs")

  @tag :tmp_dir
  test "proves actual cross-crate cleanup and borrowed updates on both exits", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Captured"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    property = Path.join(project, "Captured/Properties.lean")
    properties = File.read!(Path.join(@fixture, "CapturedProperties.lean"))
    File.write!(property, properties)

    opts = [
      roots: ["ownership_app::compose"],
      tools: @tools,
      owned_drops: :explicit,
      unwind: :captured,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Captured.Extraction",
      proof_modules: ["Captured.Properties"],
      required_properties: ~w(Captured.Properties.checked_flip Captured.Properties.compose)
    ]

    verify = fn -> Lynx.Rust.verify!(workspace, "ownership-app", opts) end
    result = verify.()
    assert [%{status: :ok}] = result.reports
    assert length(result.extraction.captured_unwind) == 2

    assert Enum.all?(
             result.extraction.captured_unwind,
             &(&1.original_signature != &1.captured_signature and &1.panic == :result_err_unit)
           )

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert Enum.any?(
             result.verification.trusted_boundary,
             &String.contains?(&1, "exceptional-exit")
           )

    assert [%{status: :ok, cached: true}] = verify.().reports

    raw = result.extraction.llbc |> File.read!() |> JSON.decode!()

    for path <- [
          ~w(std panicking begin_panic),
          ~w(core panicking panic_fmt),
          ~w(core panicking assert_failed)
        ] do
      changed = replace_panic_name(raw, Enum.map(path, &%{"Ident" => [&1, 0]}))
      refute changed == raw

      assert_raise CompileError,
                   ~r/generic or formatted panic payload behavior is unsupported/,
                   fn ->
                     Lynx.Rust.LLBC.audit!(changed, result.extraction.audit.first_party,
                       explicit_ownership: true,
                       unwind: :captured
                     )
                   end
    end

    file =
      Lynx.Rust.Proofs.file!(result.extraction, opts[:proof_modules],
        required_properties: opts[:required_properties]
      )

    export = Path.join(tmp, "captured.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom cleanupTrust : False",
          "private theorem unfinishedCleanup : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> extra <> "\n")
      assert_raise RuntimeError, ~r/Rust properties or proof audit failed/, verify
    end

    wrong = String.replace(properties, "if accepted then first else !first", "first")
    refute wrong == properties
    File.write!(property, wrong)
    assert_raise RuntimeError, ~r/native Lean project command failed/, verify
    File.write!(property, properties)

    source = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(source)
    File.write!(source, String.replace(original, "*self.0 = !*self.0;", "*self.0 = *self.0;"))
    assert_raise RuntimeError, ~r/native Lean project command failed/, verify
    File.write!(source, original)
    assert [%{status: :ok}] = verify.().reports

    File.write!(
      source,
      String.replace(original, "*self.0 = !*self.0;", "assert!(*self.0); *self.0 = !*self.0;")
    )

    assert_raise CompileError, ~r/fallible trait methods are unsupported/, verify
  end

  defp replace_panic_name(%{"Panic" => %{"name" => _} = panic} = node, name),
    do: %{node | "Panic" => %{panic | "name" => name}}

  defp replace_panic_name(map, name) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, replace_panic_name(value, name)} end)

  defp replace_panic_name(list, name) when is_list(list),
    do: Enum.map(list, &replace_panic_name(&1, name))

  defp replace_panic_name(value, _), do: value
end
