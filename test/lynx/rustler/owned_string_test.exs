defmodule Lynx.Rustler.OwnedStringTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/OwnedTextNifProperties.lean", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for owned text NIF proofs")

  @tag :tmp_dir
  test "proves actual owned UTF-8 conversion through a compiled binary NIF", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for item <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@workspace, item), Path.join(workspace, item))

    source = Path.join(workspace, "nif/src/lib.rs")

    native_source =
      File.read!(source)
      |> String.replace("LynxRustFixture.Native", "LynxOwnedTextFixture.Native")
      |> String.replace("LynxRustFixture.BinaryNative", "LynxOwnedTextFixture.Native")

    native_source =
      if @unpatched do
        "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
          Regex.replace(
            ~r/(^#\[rustler::nif[^\n]*\]\n)/m,
            native_source,
            "\\1#[verify::start_from]\n"
          )
      else
        native_source
      end

    File.write!(source, native_source)

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "OwnedText"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.join(@workspace, "proofs/.lake/packages"),
      Path.join(project, ".lake/packages")
    )

    base = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      root_attribute: if(@unpatched, do: "verify::start_from"),
      cargo: [features: ["owned-text"]],
      only: [decode_owned: 1],
      lean_project: project,
      module_prefix: "OwnedText.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(base)

    assert [%{"name" => "decode_owned", "arity" => 1, "flags" => 0} = binding] =
             discovered.bindings.bindings

    properties = File.read!(@proof) |> String.replace("__FACADE__", binding["lean_name"])
    File.write!(Path.join(project, "OwnedText/Properties.lean"), properties)

    required =
      Enum.map(
        ~w(composition decode_invalid invalid_bytes non_ascii facade_unicode facade_invalid),
        &("OwnedText.Properties." <> &1)
      )

    options = base ++ [proof_modules: ["OwnedText.Properties"], required_properties: required]
    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert Enum.any?(
             prepared.verification.external_models,
             &String.contains?(&1, "String Encoder model")
           )

    assert Enum.any?(prepared.trusted_boundary, &String.contains?(&1, "String Encoder model"))
    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    native = Path.join(tmp, "native.ex")

    File.write!(native, """
    defmodule LynxOwnedTextFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}",0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert {:ok, [LynxOwnedTextFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(native, tmp, LynxOwnedTextFixture.Native)

    {calibration, 0} =
      System.cmd(
        "elixir",
        [
          "-e",
          """
          Code.compile_file(#{inspect(native)})
          IO.inspect(Enum.map(["hé",<<195,40>>,<<240,159>>,""],&LynxOwnedTextFixture.Native.decode_owned/1))
          try do
            LynxOwnedTextFixture.Native.decode_owned(true)
          catch :error, :badarg -> IO.puts("badarg confirmed") end
          """
        ],
        cd: tmp,
        env: [{"ERL_FLAGS", "+S 2:2"}],
        stderr_to_stdout: true
      )

    assert calibration =~ ~s([ok: "hé", error: [195, 40], error: [240, 159], ok: ""])
    assert calibration =~ "badarg confirmed"

    beams =
      for {name, input, expected} <- [
            {"Unicode", "<<104,195,169>>", "{:ok,<<104,195,169>>}"},
            {"Invalid", "<<195,40>>", "{:error,[195,40]}"},
            {"Truncated", "<<240,159>>", "{:error,[240,159]}"},
            {"Empty", "<<>>", "{:ok,<<>>}"}
          ] do
        [{_, beam}] =
          Code.compile_string("""
          defmodule LynxOwnedTextFixture.#{name} do
            @compile :debug_info
            use Lynx.Laws
            law classification,
              expects: LynxOwnedTextFixture.Native.decode_owned(#{input}) == #{expected},
              proof: ~LEAN\"\"\"
              simp only [Lynx.apply,«classification:ensures/0»,
                Elixir.LynxOwnedTextFixture.Native.«decode_owned/1»,
                Elixir.LynxOwnedTextFixture.Native.«decode_owned:execution/1»]
              cbv
              \"\"\"
          end
          """)

        beam
      end

    export = Path.join(tmp, "owned-nif.export")
    reports = Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}, export: export)
    assert [] == for(r <- reports, r.status != :ok, do: r.diagnostics)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(
             Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    original = File.read!(source)

    changed =
      String.replace(
        original,
        "experiment_analysis::decode_owned(bytes)",
        "experiment_analysis::decode_owned(Vec::new())"
      )

    refute changed == original
    File.write!(source, changed)
    assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
