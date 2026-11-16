defmodule Lynx.Rustler.SliceReaderTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do:
      @moduletag(
        skip:
          "set LYNX_AENEAS_DIR to runtime tools and LYNX_FULL_MIR=1 for standard exact-read NIF laws"
      )

  @tag :tmp_dir
  test "proves byte-slice decoding through a compiled binary NIF", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxIoFixture", "LynxSliceReaderFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "SliceReader"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    properties =
      File.read!(Path.join(@fixture, "SliceReaderProperties.lean"))
      |> String.replace(
        "open Aeneas Aeneas.Std Lynx io_protocol",
        "open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol"
      )

    File.write!(Path.join(project, "SliceReader/Properties.lean"), properties)

    modules = ["SliceReader.Properties", "SliceReader.Adapter"]

    base = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      sysroot: :full_mir,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      only: [slice_word: 1],
      proof_roots: ~w(io_protocol::parse_packet io_core::slice_suffix),
      lean_project: project,
      module_prefix: "SliceReader.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(base ++ [proof_modules: ["SliceReader.Properties"]])

    assert [%{"name" => "slice_word", "arity" => 1, "flags" => 0} = binding] =
             prepared.bindings.bindings

    assert Enum.all?(prepared.external.purities, fn {_, purity} -> purity == :concurrent end)

    File.write!(Path.join(project, "SliceReader/Adapter.lean"), """
    module
    public import SliceReader.Properties
    public import SliceReader.RustlerBridge
    public section
    theorem SliceReader.Adapter.facade (binary : Lynx.Rustler.Binary) : #{binding["lean_name"]} binary = (do
      let input ← Lynx.NativeM.fromRust (Lynx.Rustler.binaryAsSlice binary)
      io_native.io_protocol.parse_packet input) := by
      simp [#{binding["lean_name"]},Lynx.NativeM.monadLift_eq]
    """)

    required =
      Enum.map(
        ~w(core_word composed_word empty_read one_read short_read empty_word suffix_valid suffix_invalid fill_short),
        &("SliceReader.Properties." <> &1)
      ) ++ ["SliceReader.Adapter.facade"]

    options = base ++ [proof_modules: modules, required_properties: required]
    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))
    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    native = Path.join(tmp, "native.ex")

    File.write!(native, """
    defmodule LynxSliceReaderFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}",0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert {:ok, [LynxSliceReaderFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(native, tmp, LynxSliceReaderFixture.Native)

    # Calibrate binary decoding and slice consumption in a separate VM.
    {calibration, 0} =
      System.cmd(
        "elixir",
        [
          "-e",
          """
          Code.compile_file(#{inspect(native)})
          first = LynxSliceReaderFixture.Native.slice_word(<<>>)
          second = LynxSliceReaderFixture.Native.slice_word(<<7,8,9>>)
          third = LynxSliceReaderFixture.Native.slice_word(<<7>>)
          fourth = LynxSliceReaderFixture.Native.slice_word(<<255,0>>)
          IO.inspect({first,second,third,fourth})
          """
        ],
        cd: tmp,
        env: [{"ERL_FLAGS", "+S 2:2"}],
        stderr_to_stdout: true
      )

    assert calibration =~ "{{:error, 1}, {:ok, {2055, 1}}, {:error, 1}, {:ok, {255, 0}}}"

    for {name, input, expected} <- [
          {"Word", "<<7,8,9>>", "{:ok,{2055,1}}"},
          {"NonUtf8", "<<255,0>>", "{:ok,{255,0}}"},
          {"Short", "<<7>>", "{:error,1}"},
          {"Empty", "<<>>", "{:error,1}"}
        ] do
      law = """
      defmodule LynxSliceReaderFixture.#{name} do
        @compile :debug_info
        use Lynx.Laws
        law classification,
          expects: LynxSliceReaderFixture.Native.slice_word(#{input}) == #{expected},
          proof: ~LEAN\"\"\"
          refine ⟨0, ?_⟩
          intro depth enough elapsed events last outcome run terminal
          apply terminal.outcome_eq.symm.trans
          apply Lynx.Outcome.eq_of_isTrue
          apply Lynx.Concurrent.checkPost_sound (depth := 128)
            (accept := fun config => config.outcome.isTrue) ?_ run terminal
          clear enough events last outcome run terminal
          simp only [Lynx.apply,«classification:ensures/0»,
            Elixir.LynxSliceReaderFixture.Native.«slice_word/1»,
            Elixir.LynxSliceReaderFixture.Native.«slice_word:execution/1»,
            SliceReader.Adapter.facade,io_native.io_protocol.parse_packet,
            io_native.io_protocol.parse_slice]
          cbv
          \"\"\"
      end
      """

      [{_, beam}] = Code.compile_string(law)

      laws = [
        native: {Lynx.Rustler, options}
      ]

      export = Path.join(tmp, name <> ".export")
      reports = Lynx.Laws.verify([beam], Keyword.put(laws, :export, export))
      assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
      guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

      for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
          do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

      assert Enum.all?(Lynx.Laws.verify([beam], laws), &(&1.status == :ok and &1.cached))
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
    end

    original = File.read!(source)

    changed =
      String.replace(original, "io_protocol::parse_packet(input.as_slice())", "Ok((0, 0))")

    refute changed == original
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert error.message =~ "SliceReader/Adapter.lean:"
    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
