defmodule Lynx.Rustler.LockedFileAwaitTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_FILE_AWAIT_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_FILE_AWAIT_DIR for shared file future proofs")

  @tag :tmp_dir
  test "retains shared file contents across guarded future cancellation and completion", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    native = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      native,
      String.replace(File.read!(native), "LynxIoFixture", "LynxLockedAwaitFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "LockedAwait"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    proof =
      File.read!(Path.join(@fixture, "LockedAwaitProperties.lean"))
      |> String.replace(
        "open Aeneas Aeneas.Std Lynx io_protocol",
        "open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol"
      )

    File.write!(Path.join(project, "LockedAwait/Properties.lean"), proof)

    File.cp!(
      Path.join(@fixture, "NativeNoPanicProperties.lean"),
      Path.join(project, "LockedAwait/Safety.lean")
    )

    properties =
      Enum.map(
        ~w(constructor unstarted_cleanup suspended_cleanup completed_cleanup
      yield_pending yield_ready resume_contract first_pending_contract caller_contract no_panic),
        &("LockedAwait.Properties." <> &1)
      )

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      cargo: [features: ["async-shared-write"]],
      only: [async_log_open: 0, async_log_write: 4, async_log_read: 2],
      execution: :runtime,
      files: :regular,
      futures: :cancelling,
      owned_drops: true,
      branching: :duplicate,
      lean_project: project,
      module_prefix: "LockedAwait.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["LockedAwait.Properties", "LockedAwait.Safety"],
      required_properties: properties,
      nonpanicking: [{"io_protocol::poll_locked_write", "LockedAwait.Properties.no_panic"}]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    bindings = Map.new(prepared.bindings.bindings, &{&1["name"], &1})

    assert %{
             "async_log_open" => %{"rust_name" => "open_request", "arity" => 0, "flags" => 2},
             "async_log_write" => %{"rust_name" => "write_request", "arity" => 4, "flags" => 2},
             "async_log_read" => %{"rust_name" => "read_request", "arity" => 2, "flags" => 2}
           } = bindings

    nif_proof =
      File.read!(Path.join(@fixture, "LockedAwaitNifProperties.lean"))
      |> String.replace("__OPEN__", bindings["async_log_open"]["lean_name"])
      |> String.replace("__WRITE__", bindings["async_log_write"]["lean_name"])

    property = Path.join(project, "LockedAwait/NifProperties.lean")
    File.write!(property, nif_proof)

    options =
      options
      |> Keyword.update!(:proof_modules, &(&1 ++ ["LockedAwait.NifProperties"]))
      |> Keyword.update!(:required_properties, &(&1 ++ ~w(LockedAwait.NifProperties.open_contract
        LockedAwait.NifProperties.write_contract LockedAwait.NifProperties.shared_cancel_resume)))

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    library = Path.join(tmp, "liblocked_await")
    File.cp!(checked.library, library <> ".so")

    stub =
      File.read!(Path.join(@fixture, "Native.exs"))
      |> String.replace("LynxIoFixture", "LynxLockedAwaitFixture")
      |> String.replace("__LIBRARY__", JSON.encode!(library))
      |> String.replace("\nend\n", """

        def log_reopen(_), do: :erlang.nif_error(:not_loaded)
        def log_repair_append(_, _, _), do: :erlang.nif_error(:not_loaded)
        def log_create(), do: :erlang.nif_error(:not_loaded)
        def log_append(_, _), do: :erlang.nif_error(:not_loaded)
        def async_log_open(), do: :erlang.nif_error(:not_loaded)
        def async_log_write(_, _, _, _), do: :erlang.nif_error(:not_loaded)
        def async_log_read(_, _), do: :erlang.nif_error(:not_loaded)
      end
      """)

    Code.compile_string(stub)
    beams = Code.compile_file(Path.join(@fixture, "LockedAwaitLaws.exs"))
    {module, beam} = Enum.find(beams, &(elem(&1, 0) == LynxLockedAwaitFixture.Laws))

    {error_module, error_beam} =
      Enum.find(beams, &(elem(&1, 0) == LynxLockedAwaitFixture.ErrorLaws))

    runtime = Path.join(tmp, "runtime")
    File.mkdir_p!(runtime)

    File.cd!(runtime, fn ->
      for law <- [:cancel_then_resume, :resume_then_cancel] do
        File.write!("journal", <<1>>)
        assert apply(module, law, [])
        assert File.read!("journal") == <<7, 8, 9, 10>>
      end

      File.rm!("journal")
      assert apply(error_module, :opening_failure, [])
    end)

    for {beam, initial, count, filename} <- [
          {beam, "LockedAwait.NifProperties.namedInitial", 2, "success"},
          {error_beam, "LockedAwait.NifProperties.rejected", 1, "error"}
        ] do
      export = Path.join(tmp, filename <> ".export")

      laws = [
        native: {Lynx.Rustler, options},
        initial_environment: initial,
        options: [maxRecDepth: 32768, maxHeartbeats: 24_000_000]
      ]

      reports = Lynx.Laws.verify([beam], Keyword.put(laws, :export, export))
      assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
      assert length(Enum.flat_map(reports, & &1.theorems)) == count
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
      assert Enum.all?(Lynx.Laws.verify([beam], laws), &(&1.status == :ok and &1.cached))
    end

    for extra <- [
          "private axiom hidden_shared_file : False",
          "private theorem unfinished_shared_file : True := by sorry"
        ] do
      File.write!(property, nif_proof <> "\n" <> extra)
      assert_raise RuntimeError, ~r/proof audit failed/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, nif_proof)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

    wrong = String.replace(nif_proof, "#[7,8,9,10]", "#[7,8,0,0]")
    refute wrong == nif_proof
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property, nif_proof)

    valid = File.read!(native)

    reversed =
      String.replace(
        valid,
        "io_protocol::poll_locked_write(&owner.file, [first, second], resume)",
        "io_protocol::poll_locked_write(&owner.file, [second, first], resume)"
      )

    refute reversed == valid
    File.write!(native, reversed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(native, valid)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
