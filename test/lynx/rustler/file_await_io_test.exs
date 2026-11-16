defmodule Lynx.Rustler.FileAwaitIoTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_FILE_AWAIT_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_FILE_AWAIT_DIR for file future I/O proofs")

  @tag :tmp_dir
  test "composes partial writes and real read-only write failures through retained resources", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    native = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      native,
      String.replace(File.read!(native), "LynxIoFixture", "LynxLockedAwaitIoFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "LockedAwait"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    for {source, target} <- [
          {"LockedAwaitProperties.lean", "Properties.lean"},
          {"LockedAwaitIoProperties.lean", "Io.lean"}
        ] do
      content =
        File.read!(Path.join(@fixture, source))
        |> String.replace(
          "open Aeneas Aeneas.Std Lynx io_protocol",
          "open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol"
        )

      File.write!(Path.join(project, "LockedAwait/" <> target), content)
    end

    properties =
      ~w(caller_contract no_panic caller_success_prefix caller_error_prefix)
      |> Enum.map(&("LockedAwait.Properties." <> &1))

    properties =
      properties ++
        Enum.map(
          ~w(partial_prefix error_prefix partial_result error_result),
          &("LockedAwait.Io." <> &1)
        )

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      cargo: [features: ["async-readonly"]],
      only: [async_log_open: 0, async_log_readonly: 0, async_log_write: 4, async_log_read: 2],
      execution: :runtime,
      files: :regular,
      futures: :cancelling,
      owned_drops: true,
      branching: :duplicate,
      lean_project: project,
      module_prefix: "LockedAwait.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["LockedAwait.Properties", "LockedAwait.Io"],
      required_properties: properties,
      nonpanicking: [{"io_protocol::poll_locked_write", "LockedAwait.Properties.no_panic"}]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    bindings = Map.new(prepared.bindings.bindings, &{&1["name"], &1})

    assert %{
             "async_log_readonly" => %{
               "rust_name" => "readonly_request",
               "arity" => 0,
               "flags" => 2
             }
           } = bindings

    replacements = [
      {"__OPEN__", "async_log_open"},
      {"__WRITE__", "async_log_write"},
      {"__READONLY__", "async_log_readonly"}
    ]

    for {source, target} <- [
          {"LockedAwaitNifProperties.lean", "NifProperties.lean"},
          {"LockedAwaitIoNifProperties.lean", "IoNif.lean"}
        ] do
      content =
        Enum.reduce(replacements, File.read!(Path.join(@fixture, source)), fn {marker, name},
                                                                              content ->
          String.replace(content, marker, bindings[name]["lean_name"])
        end)

      File.write!(Path.join(project, "LockedAwait/" <> target), content)
    end

    options =
      options
      |> Keyword.update!(
        :proof_modules,
        &(&1 ++ ["LockedAwait.NifProperties", "LockedAwait.IoNif"])
      )
      |> Keyword.update!(:required_properties, &(&1 ++ ~w(LockedAwait.IoNif.readonly_contract
        LockedAwait.IoNif.write_outcomes)))

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    library = Path.join(tmp, "libfile_io")
    File.cp!(checked.library, library <> ".so")
    [{module, exports}] = Map.to_list(checked.external.native_exports)
    assert module == LynxLockedAwaitIoFixture.Native

    functions =
      Enum.map_join(exports, "\n", fn {name, arity} ->
        "def #{name}(#{Enum.join(List.duplicate("_", arity), ", ")}), do: :erlang.nif_error(:not_loaded)"
      end)

    Code.compile_string("""
    defmodule #{inspect(module)} do
      @compile :debug_info
      @on_load :load
      def load, do: :erlang.load_nif(to_charlist(#{JSON.encode!(library)}), 0)
      #{functions}
    end
    """)

    beams = Code.compile_file(Path.join(@fixture, "LockedAwaitIoLaws.exs"))
    runtime = Path.join(tmp, "runtime")
    File.mkdir_p!(runtime)

    File.cd!(runtime, fn ->
      for {module, name} <- [
            {LynxLockedAwaitIoFixture.ReadOnlyLaws, :failed_writes_keep_resource},
            {LynxLockedAwaitIoFixture.DecodeLaws, :bad_argument_preserves_failed_write}
          ] do
        File.write!("journal", <<7, 8>>)
        assert apply(module, name, [])
        assert File.read!("journal") == <<7, 8>>
      end
    end)

    for {module, beam} <- beams do
      {initial, filename} =
        case module do
          LynxLockedAwaitIoFixture.ReadOnlyLaws -> {"LockedAwait.IoNif.readOnly", "readonly"}
          LynxLockedAwaitIoFixture.DecodeLaws -> {"LockedAwait.IoNif.decoding", "decode"}
          LynxLockedAwaitIoFixture.PartialLaws -> {"LockedAwait.IoNif.shortWrite", "partial"}
        end

      laws = [
        native: {Lynx.Rustler, options},
        initial_environment: initial,
        options: [maxRecDepth: 16384, maxHeartbeats: 12_000_000]
      ]

      export = Path.join(tmp, filename <> ".export")
      reports = Lynx.Laws.verify([beam], Keyword.put(laws, :export, export))
      assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
      assert length(Enum.flat_map(reports, & &1.theorems)) == 1
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
      assert Enum.all?(Lynx.Laws.verify([beam], laws), &(&1.status == :ok and &1.cached))
    end

    {_, readonly_beam} = Enum.find(beams, &(elem(&1, 0) == LynxLockedAwaitIoFixture.ReadOnlyLaws))

    rejected =
      Lynx.Laws.verify([readonly_beam],
        native: {Lynx.Rustler, options},
        initial_environment: "LockedAwait.IoNif.unadmittedError",
        options: [maxRecDepth: 16384, maxHeartbeats: 12_000_000]
      )

    assert [%{status: :error, diagnostics: diagnostics}] =
             Enum.filter(rejected, &(&1.status != :ok))

    assert Enum.any?(diagnostics, &String.contains?(&1.message, "⊢ False"))

    proof = Path.join(project, "LockedAwait/IoNif.lean")
    valid = File.read!(proof)

    for extra <- [
          "private axiom hidden_io_admission : False",
          "private theorem unfinished_io_cleanup : True := by sorry"
        ] do
      File.write!(proof, valid <> "\n" <> extra)
      assert_raise RuntimeError, ~r/proof audit failed/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(proof, valid)
    wrong = String.replace(valid, "then #[7] else #[1]", "then #[1] else #[1]")
    refute valid == wrong
    File.write!(proof, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(proof, valid)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
