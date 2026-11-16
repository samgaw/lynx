defmodule Lynx.Rustler.IoPayloadTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do:
      @moduletag(
        skip:
          "set LYNX_AENEAS_DIR to runtime tools and LYNX_FULL_MIR=1 for IO classification NIF laws"
      )

  @tag :tmp_dir
  test "proves classified read errors through a renamed compiled dirty IO NIF", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxIoFixture", "LynxIoPayloadFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "IoPayload"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    modules = ["IoPayload.Properties", "IoPayload.Adapter"]

    base = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      sysroot: :full_mir,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      only: [read_retryable: 0],
      proof_roots: ~w(io_protocol::error_is_retryable io_protocol::read_is_retryable),
      lean_project: project,
      module_prefix: "IoPayload.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert [%{"name" => "read_retryable", "arity" => 0, "flags" => 2} = binding] =
             prepared.bindings.bindings

    assert Enum.all?(prepared.external.purities, fn {_, purity} -> purity == :concurrent end)

    properties =
      File.read!(Path.join(@fixture, "IoPayloadProperties.lean"))
      |> String.replace(
        "open Aeneas Aeneas.Std Lynx io_protocol",
        "open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol"
      )

    File.write!(Path.join(project, "IoPayload/Properties.lean"), properties)

    File.write!(Path.join(project, "IoPayload/Adapter.lean"), """
    module
    public import IoPayload.Properties
    public section
    theorem IoPayload.Adapter.facade : #{binding["lean_name"]} =
        io_native.io_protocol.read_is_retryable IoPayload.Properties.path := by
      simp [#{binding["lean_name"]},IoPayload.Properties.path]
    """)

    required =
      Enum.map(
        ~w(core_spec borrowed_kind classified read_contract open_error read_error read_success scenarios every_run rejected),
        &("IoPayload.Properties." <> &1)
      ) ++ ["IoPayload.Adapter.facade"]

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
    defmodule LynxIoPayloadFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}",0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert {:ok, [LynxIoPayloadFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(native, tmp, LynxIoPayloadFixture.Native)

    # Isolate the process cwd while calibrating actual missing, complete and EOF reads.
    {calibration, 0} =
      System.cmd(
        "elixir",
        [
          "-e",
          """
          Code.compile_file(#{inspect(native)})
          first = LynxIoPayloadFixture.Native.read_retryable()
          File.write!("missing",<<7>>)
          second = LynxIoPayloadFixture.Native.read_retryable()
          File.write!("missing",<<>>)
          third = LynxIoPayloadFixture.Native.read_retryable()
          IO.inspect({first,second,third})
          """
        ],
        cd: tmp,
        env: [{"ERL_FLAGS", "+S 2:2"}],
        stderr_to_stdout: true
      )

    assert calibration =~ "{false, false, false}"

    for {expected, cases} <- [{true, ["interrupted"]}, {false, ~w(missing other complete eof)}] do
      name = if expected, do: "Retryable", else: "NotRetryable"

      law = """
      defmodule LynxIoPayloadFixture.#{name} do
        @compile :debug_info
        use Lynx.Laws
        law classification,
          expects: LynxIoPayloadFixture.Native.read_retryable() == #{expected},
          proof: ~LEAN\"\"\"
          refine ⟨0, ?_⟩
          intro depth enough elapsed events last outcome run terminal
          apply terminal.outcome_eq.symm.trans
          apply Lynx.Outcome.eq_of_isTrue
          apply Lynx.Concurrent.checkPost_sound (depth := 128)
            (accept := fun config => config.outcome.isTrue) ?_ run terminal
          clear enough events last outcome run terminal
          simp only [Lynx.apply,«classification:ensures/0»,
            Elixir.LynxIoPayloadFixture.Native.«read_retryable/0»,
            Elixir.LynxIoPayloadFixture.Native.«read_retryable:execution/0»,
            IoPayload.Adapter.facade,IoPayload.Properties.read_contract,
            IoPayload.Properties.finishRead,IoPayload.Properties.classifyDrop,
            io_native.io_protocol.error_is_retryable,IoPayload.Properties.core_spec]
          cbv
          \"\"\"
      end
      """

      [{_, beam}] = Code.compile_string(law)

      for initial <- cases do
        laws = [
          native: {Lynx.Rustler, options},
          initial_environment: "IoPayload.Properties." <> initial
        ]

        export = Path.join(tmp, initial <> ".export")
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

      if expected do
        for bad <- ~w(noMetadata unknownKind) do
          reports =
            Lynx.Laws.verify([beam],
              native: {Lynx.Rustler, options},
              initial_environment: "IoPayload.Properties." <> bad
            )

          assert Enum.any?(reports, &(&1.status == :error))
        end
      end
    end

    original = File.read!(source)
    changed = String.replace(original, "io_protocol::read_is_retryable(\"missing\")", "false")
    refute changed == original
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert error.message =~ "IoPayload/Adapter.lean:"
    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
