defmodule Lynx.Rust.StringViewsTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for borrowed text proofs")

  @tag :tmp_dir
  test "proves internal string byte views without NIF exposure", %{tmp_dir: tmp} do
    workspace = workspace(tmp)
    project = project(tmp, "TextCore")

    File.cp!(
      Path.join(@proofs, "TextViewsCore.lean"),
      Path.join(project, "TextCore/Properties.lean")
    )

    options = [
      tools: @tools,
      lean_project: project,
      module_prefix: "TextCore.Extraction",
      roots:
        Enum.map(~w(text_bytes text_length text_empty), &("experiment_core::protocol::" <> &1)),
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["TextCore.Properties"],
      required_properties:
        Enum.map(~w(bytes_spec length_spec empty_spec), &("TextCore.Properties." <> &1))
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-core", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-core", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, ["TextCore.Properties"])
    export = Path.join(tmp, "text-core.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    replay(project, export)

    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)
    changed = String.replace(original, "text.len()", "0")
    assert changed != original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-core", options)
    end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-core", options).reports
  end

  @tag :tmp_dir
  test "composes borrowed text parsing through a renamed dirty NIF", %{tmp_dir: tmp} do
    workspace = workspace(tmp)
    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      File.read!(source)
      |> String.replace("LynxRustFixture.Native", "LynxRustFixture.TextNative")
      |> String.replace("LynxRustFixture.BinaryNative", "LynxRustFixture.TextNative")
    )

    project = project(tmp, "TextViews")

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      cargo: [features: ["text-views"]],
      only: [text_payload: 2],
      lean_project: project,
      module_prefix: "TextViews.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "text_payload",
               "arity" => 2,
               "flags" => 1,
               "result" => %{"result" => [%{"option" => "u64"}, "u8"]}
             } = binding
           ] = discovered.bindings.bindings

    proof =
      File.read!(Path.join(@proofs, "TextViews.lean"))
      |> String.replace("__FACADE__", binding["lean_name"])

    File.write!(Path.join(project, "TextViews/Properties.lean"), proof)

    options =
      options ++
        [
          proof_modules: ["TextViews.Properties"],
          required_properties:
            Enum.map(
              ~w(core_bytes payload_spec exact_bytes caller_spec invalid_spec inside_character facade_unicode facade_inside_character facade_truncated facade_invalid),
              &("TextViews.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert Enum.any?(
             prepared.verification.unverified_external_calls,
             &(&1.implementation_verified == false and String.contains?(&1.rust_name, "as_bytes"))
           )

    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    [{native, _}] =
      Code.compile_string("""
      defmodule LynxRustFixture.TextNative do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
        #{Enum.join(stubs, "\n")}
      end
      """)

    for {input, header, expected} <- [
          {"", 0, {:ok, 0}},
          {"", 1, {:ok, nil}},
          {"é", 0, {:ok, 2}},
          {"é", 1, {:ok, 1}},
          {"é", 2, {:ok, 0}},
          {"é", 3, {:ok, nil}},
          {<<255>>, 0, {:error, 4}},
          {<<194>>, 0, {:error, 4}},
          {"é", 257, {:ok, 1}}
        ],
        do: assert(apply(native, :text_payload, [input, header]) == expected)

    for args <- [[true, 0], ["é", -1], ["é", 4_294_967_296]],
        do: assert_raise(ArgumentError, fn -> apply(native, :text_payload, args) end)

    [{_, beam}] = Code.compile_file(Path.join(@workspace, "elixir/text_views_laws.ex"))
    export = Path.join(tmp, "text.export")
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
             &(&1.status == :ok and &1.cached)
           )

    replay(project, export)

    rust = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(rust)
    changed = String.replace(original, "text.as_bytes()", "&[]")
    assert changed != original
    File.write!(rust, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(rust, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end

  defp workspace(tmp) do
    path = Path.join(tmp, "workspace")
    File.mkdir_p!(path)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@workspace, entry), Path.join(path, entry))

    path
  end

  defp project(tmp, namespace) do
    path = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(path, namespace))
    packages = Path.join(@workspace, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(path, ".lake"))
      File.ln_s!(packages, Path.join(path, ".lake/packages"))
    end

    path
  end

  defp replay(project, export) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
