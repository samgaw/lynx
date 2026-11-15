defmodule Lynx.Rustler.SignedStateTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_SIGNED_DIR")
  @moduletag timeout: 1_800_000
  unless @tools, do: @moduletag(skip: "set LYNX_NATIVE_SIGNED_DIR for signed native state proofs")

  @tag :tmp_dir
  test "composes signed checked updates through a real mutex and compiled NIF", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")
    File.write!(rust, String.replace(File.read!(rust), "LynxAtomicFixture", "LynxSignedFixture"))
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Signed"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    common = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      branching: :duplicate,
      root_attribute: "lynx::signed",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Signed.Extraction",
      only: [signed_adjust: 2]
    ]

    prepared = Lynx.Rustler.prepare!(common)
    [binding] = prepared.bindings.bindings

    properties =
      File.read!(Path.join(@fixture, "SignedProperties.lean"))
      |> String.replace("__NIF__", binding["lean_name"])

    property = Path.join(project, "Signed/Properties.lean")
    File.write!(property, properties)

    options =
      common ++
        [
          proof_modules: ["Signed.Properties"],
          required_properties:
            Enum.map(
              ~w(adjusted locked_contract adjusted_eq facade_contract facade_run),
              &("Signed.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    assert File.read!(Path.join(project, "Signed/Extraction/NativeCodecs.lean")) =~ "i64"

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxSignedFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    native = LynxSignedFixture.Native
    assert apply(native, :signed_adjust, [-7, 3]) == {true, -4}
    assert apply(native, :signed_adjust, [7, -11]) == {true, -4}
    assert apply(native, :signed_adjust, [-7, 11]) == {true, 4}

    assert apply(native, :signed_adjust, [9_223_372_036_854_775_807, 1]) ==
             {false, 9_223_372_036_854_775_807}

    assert apply(native, :signed_adjust, [-9_223_372_036_854_775_808, -1]) ==
             {false, -9_223_372_036_854_775_808}

    for args <- [[9_223_372_036_854_775_808, 0], [-9_223_372_036_854_775_809, 0], [0, false]],
        do: assert_raise(ArgumentError, fn -> apply(native, :signed_adjust, args) end)

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/signed_laws.ex"))

    for law <-
          ~w(negative_credit negative_debit cross_zero positive_overflow negative_overflow above_range below_range invalid_delta)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "signed-laws.export")

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 8192, maxHeartbeats: 16_000_000]
    ]

    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))

    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 8
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Signed.Properties"],
        module: "Signed.ExportAudit"
      )

    native_export = Path.join(tmp, "signed-native.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [audit], export: native_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", native_export] ++ sandbox)

    assert status == 0, output

    assert Enum.all?(
             Lynx.Laws.verify([beam], law_options),
             &(&1.status == :ok and &1.cached)
           )

    laws = File.read!(Path.join(workspace, "elixir/signed_laws.ex"))
    incorrect = String.replace(laws, "== {true, 4}", "== {true, -4}")
    assert incorrect != laws

    [{_, incorrect_beam}] =
      incorrect
      |> String.replace(
        "defmodule LynxSignedFixture.Laws",
        "defmodule LynxSignedFixture.FalseLaws"
      )
      |> Code.compile_string("signed_false_laws.ex")

    rejected = Lynx.Laws.verify([incorrect_beam], law_options)
    assert Enum.any?(rejected, &(&1.status == :error))

    assert Enum.any?(Enum.flat_map(rejected, & &1.diagnostics), fn diagnostic ->
             diagnostic[:declaration] == "cross_zero/0" and diagnostic[:severity] == :error
           end)

    for invalid <- [
          "private axiom uncheckedSignedState : False",
          "private theorem unfinishedSignedState : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, properties)

    source = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(source)
    altered = String.replace(original, "balance.value = value;", "balance.value = delta;")
    assert altered != original
    File.write!(source, altered)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
