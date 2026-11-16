defmodule Lynx.Rustler.ErrorKindTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for compiled ErrorKind laws")

  @tag :tmp_dir
  test "links actual standard error classification through compiled Rustler exports", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "native/src/lib.rs")
    File.write!(source, String.replace(File.read!(source), "LynxIoFixture", "LynxIoKindsFixture"))
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "IoKinds"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      sysroot: :full_mir,
      only: [classify_end_of_file: 0, classify_interrupted_read: 0],
      lean_project: project,
      module_prefix: "IoKinds.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(options)

    binding = fn name ->
      Enum.find(prepared.bindings.bindings, &(&1["name"] == name))["lean_name"]
    end

    properties =
      File.read!(Path.join(@fixture, "ErrorKindProperties.lean"))
      |> String.replace(
        "open Aeneas Aeneas.Std io_protocol",
        "open Aeneas Aeneas.Std io_native io_native.io_protocol"
      )

    properties =
      properties <>
        """

        namespace IoKinds.Properties
        theorem eof_facade : #{binding.("classify_end_of_file")} = Aeneas.Std.RustM.ok true := by
          simp [#{binding.("classify_end_of_file")}, composition, truncated]
        theorem interrupted_facade : #{binding.("classify_interrupted_read")} = Aeneas.Std.RustM.ok false := by
          simp [#{binding.("classify_interrupted_read")}, composition, truncated]
        end IoKinds.Properties
        """

    property = Path.join(project, "IoKinds/Properties.lean")
    File.write!(property, properties)

    options =
      options ++
        [
          proof_modules: ["IoKinds.Properties"],
          required_properties:
            Enum.map(
              ~w(core_spec composition interruption eof_facade interrupted_facade),
              &("IoKinds.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))
    assert Enum.all?(prepared.external.purities, fn {_, purity} -> purity == :pure end)
    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    path = Path.join(tmp, "native.ex")

    File.write!(path, """
    defmodule LynxIoKindsFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}",0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert {:ok, [LynxIoKindsFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(path, tmp, LynxIoKindsFixture.Native)

    assert apply(LynxIoKindsFixture.Native, :classify_end_of_file, [])
    refute apply(LynxIoKindsFixture.Native, :classify_interrupted_read, [])

    [{_, beam}] =
      Code.compile_string("""
      defmodule LynxIoKindsFixture.Laws do
        @compile :debug_info
        use Lynx.Laws
        law end_of_file,
          expects: LynxIoKindsFixture.Native.classify_end_of_file() == true,
          proof: ~LEAN\"\"\"
          simp [«end_of_file:ensures/0», Elixir.LynxIoKindsFixture.Native.«classify_end_of_file/0»,
            Elixir.LynxIoKindsFixture.Native.«classify_end_of_file:execution/0»,
            IoKinds.Properties.eof_facade, Lynx.Rustler.execute, Lynx.Rustler.encodeBool,
            Erlang.erlang.«==/2»]
          \"\"\"
        law interruption,
          expects: LynxIoKindsFixture.Native.classify_interrupted_read() == false,
          proof: ~LEAN\"\"\"
          simp [«interruption:ensures/0», Elixir.LynxIoKindsFixture.Native.«classify_interrupted_read/0»,
            Elixir.LynxIoKindsFixture.Native.«classify_interrupted_read:execution/0»,
            IoKinds.Properties.interrupted_facade, Lynx.Rustler.execute, Lynx.Rustler.encodeBool,
            Erlang.erlang.«==/2»]
          \"\"\"
      end
      """)

    export = Path.join(tmp, "kinds.export")
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    original = File.read!(source)

    changed =
      String.replace(
        original,
        "io_protocol::truncated_input(std::io::ErrorKind::UnexpectedEof)",
        "io_protocol::truncated_input(std::io::ErrorKind::Interrupted)"
      )

    refute changed == original
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert error.message =~ "IoKinds/Properties.lean:"
    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
