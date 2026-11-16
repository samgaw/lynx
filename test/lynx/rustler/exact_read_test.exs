defmodule Lynx.Rustler.ExactReadTest do
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
  test "proves classified exact reads through a renamed compiled dirty IO NIF", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxIoFixture", "LynxExactReadFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "ExactRead"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    properties =
      File.read!(Path.join(@fixture, "ExactReadProperties.lean"))
      |> String.replace(
        "open Aeneas Aeneas.Std Lynx io_protocol",
        "open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol"
      )

    File.write!(Path.join(project, "ExactRead/Properties.lean"), properties)

    modules = ["ExactRead.Properties", "ExactRead.Adapter"]

    base = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      sysroot: :full_mir,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      nonpanicking: [{"io_core::fill_exact", "ExactRead.Properties.fill_no_panic"}],
      only: [read_exact_word: 0],
      proof_roots: ~w(io_protocol::optional_exact_word io_protocol::read_exact_optional),
      lean_project: project,
      module_prefix: "ExactRead.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(base ++ [proof_modules: ["ExactRead.Properties"]])

    assert [%{"name" => "read_exact_word", "arity" => 0, "flags" => 2} = binding] =
             prepared.bindings.bindings

    assert Enum.all?(prepared.external.purities, fn {_, purity} -> purity == :concurrent end)

    adapter = File.read!(Path.join(@fixture, "ExactReadNifState.lean"))

    File.write!(
      Path.join(project, "ExactRead/Adapter.lean"),
      adapter <>
        """
        theorem ExactRead.Adapter.facade : #{binding["lean_name"]} =
            io_native.io_protocol.read_exact_optional (Aeneas.Std.toStr "input") := by
          simp [#{binding["lean_name"]}]
        """
    )

    required =
      Enum.map(
        ~w(empty_input eof_contract eof_input partial_eof complete_read interrupted_retry other_error complete_prefix word_complete caller_complete eof_prefix word_eof caller_eof fill_no_panic),
        &("ExactRead.Properties." <> &1)
      ) ++ ["ExactRead.Adapter.facade"]

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
    defmodule LynxExactReadFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}",0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert {:ok, [LynxExactReadFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(native, tmp, LynxExactReadFixture.Native)

    # Isolate the process cwd while calibrating actual missing, complete and EOF reads.
    {calibration, 0} =
      System.cmd(
        "elixir",
        [
          "-e",
          """
          Code.compile_file(#{inspect(native)})
          first = LynxExactReadFixture.Native.read_exact_word()
          File.write!("input",<<7,8>>)
          second = LynxExactReadFixture.Native.read_exact_word()
          File.write!("input",<<7>>)
          third = LynxExactReadFixture.Native.read_exact_word()
          File.write!("input",<<>>)
          fourth = LynxExactReadFixture.Native.read_exact_word()
          IO.inspect({first,second,third,fourth})
          """
        ],
        cd: tmp,
        env: [{"ERL_FLAGS", "+S 2:2"}],
        stderr_to_stdout: true
      )

    assert calibration =~ "{{:error, 2}, {:ok, 2055}, {:ok, nil}, {:ok, nil}}"

    for {name, expected, cases} <- [
          {"Word", "{:ok,2055}", ["complete"]},
          {"Eof", "{:ok,nil}", ~w(short eof interrupted)},
          {"ReadError", "{:error,1}", ["other"]},
          {"OpenError", "{:error,2}", ["missing"]}
        ] do
      law = """
      defmodule LynxExactReadFixture.#{name} do
        @compile :debug_info
        use Lynx.Laws
        law classification,
          expects: LynxExactReadFixture.Native.read_exact_word() == #{expected},
          proof: ~LEAN\"\"\"
          refine ⟨0, ?_⟩
          intro depth enough elapsed events last outcome run terminal
          apply terminal.outcome_eq.symm.trans
          apply Lynx.Outcome.eq_of_isTrue
          apply Lynx.Concurrent.checkPost_sound (depth := 128)
            (accept := fun config => config.outcome.isTrue) ?_ run terminal
          clear enough events last outcome run terminal
          simp only [Lynx.apply,«classification:ensures/0»,
            Elixir.LynxExactReadFixture.Native.«read_exact_word/0»,
            Elixir.LynxExactReadFixture.Native.«read_exact_word:execution/0»,
            ExactRead.Adapter.facade,io_native.io_protocol.read_exact_optional,
            io_native.io_protocol.optional_exact_word,ExactRead.Properties.kind_eq]
          cbv
          \"\"\"
      end
      """

      [{_, beam}] = Code.compile_string(law)

      for initial <- cases do
        laws = [
          native: {Lynx.Rustler, options},
          initial_environment: "ExactRead.Adapter." <> initial
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
    end

    original = File.read!(source)

    changed =
      String.replace(original, "io_protocol::read_exact_optional(\"input\")", "Ok(Some(0))")

    refute changed == original
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert error.message =~ "ExactRead/Adapter.lean:"
    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
