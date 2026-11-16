defmodule Lynx.Rustler.FileAwaitTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_FILE_AWAIT_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_FILE_AWAIT_DIR for owned file suspension proofs")

  @tag :tmp_dir
  test "composes actual file future cancellation and completion through compiled NIF laws", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    native = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      native,
      String.replace(File.read!(native), "LynxIoFixture", "LynxFileAwaitFixture")
    )

    rust_project = project(tmp, "rust")
    property = Path.join(rust_project, "FileAwait/Properties.lean")
    original = File.read!(Path.join(@fixture, "FileAwaitProperties.lean"))
    File.write!(property, original)

    properties =
      ~w(yield_pending yield_ready constructor unstarted_cleanup suspended_cleanup completed_cleanup resume_contract first_pending_contract first_ready cancellation_ready resume_ready caller_contract caller_ready partial_write_before_pending cancellation_or_completion_retains_write repoll_completed_panics)
      |> Enum.map(&("FileAwait.Properties." <> &1))

    common = [
      tools: @tools,
      execution: :runtime,
      files: :regular,
      futures: :cancelling,
      owned_drops: true,
      branching: :duplicate
    ]

    rust =
      common ++
        [
          roots: ~w(io_protocol::suspended_write io_protocol::poll_write),
          lean_project: rust_project,
          module_prefix: "FileAwait.Extraction",
          build_dir: Path.join(tmp, "rust-build"),
          proof_modules: ["FileAwait.Properties"],
          required_properties: properties
        ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", rust)
    assert [%{status: :ok}] = result.reports
    assert [_ | _] = result.extraction.native_drops

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :cross_crate_contract and
               guarantee.theorem == "FileAwait.Properties.first_pending_contract" and
               "FileAwait.Properties.yield_pending" in guarantee.contracts_used
           end)

    assert File.read!(Path.join(rust_project, "FileAwait/Extraction/Funs.lean")) =~
             "Lynx.NativeM.fail undef"

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "physical descriptor reclamation")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", rust).reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, rust[:proof_modules],
        required_properties: properties
      )

    export = Path.join(tmp, "rust.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(rust_project, [file], export: export)
    check_export(rust_project, export)

    assert_raise CompileError, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", Keyword.delete(rust, :files))
    end

    project = project(tmp, "nif")

    proof =
      String.replace(
        original,
        "open Aeneas Aeneas.Std Lynx io_protocol",
        "open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol"
      )

    File.write!(Path.join(project, "FileAwait/Properties.lean"), proof)

    options =
      common ++
        [
          workspace: workspace,
          package: "io-native",
          cargo: [features: ["async-write"]],
          only: [write_poll: 3],
          proof_roots: ~w(io_protocol::suspended_write io_protocol::poll_write),
          lean_project: project,
          module_prefix: "FileAwait.Extraction",
          build_dir: Path.join(tmp, "nif-build"),
          proof_modules: ["FileAwait.Properties"],
          required_properties: properties
        ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "write_poll",
               "rust_name" => "write_poll_request",
               "arity" => 3,
               "flags" => 2
             } = binding
           ] = prepared.bindings.bindings

    nif_proof =
      File.read!(Path.join(@fixture, "FileAwaitNifProperties.lean"))
      |> String.replace("__WRITE__", binding["lean_name"])

    nif_property = Path.join(project, "FileAwait/NifProperties.lean")
    File.write!(nif_property, nif_proof)

    options =
      options
      |> Keyword.update!(:proof_modules, &(&1 ++ ["FileAwait.NifProperties"]))
      |> Keyword.update!(
        :required_properties,
        &(&1 ++
            ~w(FileAwait.NifProperties.facade_contract FileAwait.NifProperties.cancellation_and_completion_close FileAwait.NifProperties.every_completed_call FileAwait.NifProperties.opening_error_consumes_payload))
      )

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    library = Path.join(tmp, "libfile_await")
    File.cp!(checked.library, library <> ".so")

    stub =
      File.read!(Path.join(@fixture, "Native.exs"))
      |> String.replace("LynxIoFixture", "LynxFileAwaitFixture")
      |> String.replace("__LIBRARY__", JSON.encode!(library))
      |> String.replace(
        "\nend\n",
        "\n  def write_poll(_, _, _), do: :erlang.nif_error(:not_loaded)\nend\n"
      )

    Code.compile_string(stub)
    beams = Code.compile_file(Path.join(@fixture, "FileAwaitLaws.exs"))
    {module, beam} = Enum.find(beams, &(elem(&1, 0) == LynxFileAwaitFixture.Laws))

    {error_module, error_beam} =
      Enum.find(beams, &(elem(&1, 0) == LynxFileAwaitFixture.ErrorLaws))

    runtime = Path.join(tmp, "runtime")
    File.mkdir_p!(runtime)

    File.cd!(runtime, fn ->
      for law <- ~w(accepted cancelled narrowed decoder_preserves_io)a do
        File.write!("journal", <<1>>)
        assert apply(module, law, [])
        assert File.read!("journal") == <<7, 8>>
      end

      File.rm!("journal")
      assert apply(error_module, :opening_failure, [])
      refute File.exists?("journal")
    end)

    laws = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 16384, maxHeartbeats: 12_000_000]
    ]

    for {beam, initial, count, filename} <- [
          {beam, "FileAwait.NifProperties.initial", 4, "success"},
          {error_beam, "FileAwait.NifProperties.rejected", 1, "error"}
        ] do
      law_options = Keyword.put(laws, :initial_environment, initial)
      export = Path.join(tmp, filename <> ".export")
      reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
      assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
      assert length(Enum.flat_map(reports, & &1.theorems)) == count
      check_export(project, export)
      assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
    end

    for extra <- [
          "private axiom hidden_file_assumption : False",
          "private theorem unfinished_file : True := by sorry"
        ] do
      File.write!(nif_property, nif_proof <> "\n" <> extra)
      assert_raise RuntimeError, ~r/proof audit failed/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(nif_property, nif_proof)

    wrong =
      String.replace(
        original,
        "⟨⟨#[7]⟩, ⟨#[1]⟩, 1, .nil⟩",
        "⟨⟨#[7]⟩, ⟨#[7]⟩, 1, .nil⟩"
      )

    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", rust)
    end

    File.write!(property, original)
    source = Path.join(workspace, "protocol/src/lib.rs")
    valid = File.read!(source)

    broken =
      valid
      |> String.replace("    io_core::yield_once().await;\n", "")
      |> String.replace(
        "    let reply = match io_core::write_once(&mut file, &bytes)",
        "    io_core::yield_once().await;\n    let reply = match io_core::write_once(&mut file, &bytes)"
      )

    refute broken == valid
    File.write!(source, broken)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", rust)
    end

    panicking =
      String.replace(
        valid,
        "    io_core::yield_once().await;",
        "    io_core::yield_once().await;\n    panic!();"
      )

    refute panicking == valid
    File.write!(source, panicking)

    error = assert_raise CompileError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", rust) end
    assert error.file =~ "protocol/src/lib.rs"

    File.write!(source, valid)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", rust).reports
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end

  defp project(tmp, name) do
    project = Path.join(tmp, name)
    File.mkdir_p!(Path.join(project, "FileAwait"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    project
  end

  defp check_export(project, export) do
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
