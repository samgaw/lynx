defmodule Lynx.Rustler.CapturedFilesTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_FILE_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_FILE_DIR for captured file cleanup proofs")

  @tag :tmp_dir
  test "composes file and OS-error cleanup with cross-crate writes and compiled NIF panics", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    native = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      native,
      String.replace(File.read!(native), "LynxIoFixture", "LynxCapturedIoFixture")
    )

    rust_project = project(tmp, "rust")
    property = Path.join(rust_project, "CapturedFile/Properties.lean")
    original = File.read!(Path.join(@fixture, "CapturedFileProperties.lean"))
    File.write!(property, original)

    properties =
      ~w(write_contract error_contract mutex_contract write_ready admitted_error_cleanup partial_write_and_panic missing_error_cutoff custom_error_cutoff mutex_panic_closes missing_close_cutoff)
      |> Enum.map(&("CapturedFile.Properties." <> &1))

    common = [
      tools: @tools,
      execution: :runtime,
      files: :regular,
      unwind: :captured,
      owned_drops: true,
      branching: :duplicate
    ]

    rust =
      common ++
        [
          roots:
            ~w(io_protocol::checked_write io_protocol::checked_error io_protocol::checked_file_mutex),
          lean_project: rust_project,
          module_prefix: "CapturedFile.Extraction",
          build_dir: Path.join(tmp, "rust-build"),
          proof_modules: ["CapturedFile.Properties"],
          required_properties: properties
        ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", rust)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.extraction.native_drops, & &1.unwind)
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

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

    File.write!(Path.join(project, "CapturedFile/Properties.lean"), proof)

    options =
      common ++
        [
          workspace: workspace,
          package: "io-native",
          cargo: [features: ["captured-write"]],
          only: [checked_write: 2],
          proof_roots: ~w(io_protocol::checked_error io_protocol::checked_file_mutex),
          lean_project: project,
          module_prefix: "CapturedFile.Extraction",
          build_dir: Path.join(tmp, "nif-build"),
          proof_modules: ["CapturedFile.Properties"],
          required_properties: properties
        ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "checked_write",
               "rust_name" => "checked_write_request",
               "arity" => 2,
               "flags" => 2,
               "captured_unwind" => true
             } = binding
           ] = prepared.bindings.bindings

    nif_proof =
      File.read!(Path.join(@fixture, "CapturedFileNifProperties.lean"))
      |> String.replace("__WRITE__", binding["lean_name"])

    nif_property = Path.join(project, "CapturedFile/NifProperties.lean")
    File.write!(nif_property, nif_proof)

    options =
      options
      |> Keyword.update!(:proof_modules, &(&1 ++ ["CapturedFile.NifProperties"]))
      |> Keyword.update!(
        :required_properties,
        &(&1 ++
            ~w(CapturedFile.NifProperties.facade_contract CapturedFile.NifProperties.retains_write_without_sync CapturedFile.NifProperties.every_completed_call CapturedFile.NifProperties.opening_error_consumes_payload))
      )

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    library = Path.join(tmp, "libcaptured_io")
    File.cp!(checked.library, library <> ".so")

    stub =
      File.read!(Path.join(@fixture, "Native.exs"))
      |> String.replace("LynxIoFixture", "LynxCapturedIoFixture")
      |> String.replace("__LIBRARY__", JSON.encode!(library))
      |> String.replace(
        "\nend\n",
        "\n  def checked_write(_, _), do: :erlang.nif_error(:not_loaded)\nend\n"
      )

    Code.compile_string(stub)
    beams = Code.compile_file(Path.join(@fixture, "CapturedFileLaws.exs"))
    {module, beam} = Enum.find(beams, &(elem(&1, 0) == LynxCapturedIoFixture.Laws))

    {error_module, error_beam} =
      Enum.find(beams, &(elem(&1, 0) == LynxCapturedIoFixture.ErrorLaws))

    runtime = Path.join(tmp, "runtime")
    File.mkdir_p!(runtime)

    File.cd!(runtime, fn ->
      for law <- ~w(accepted rejected decoder_preserves_io)a do
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
          {beam, "CapturedFile.NifProperties.initial", 3, "success"},
          {error_beam, "CapturedFile.NifProperties.rejected", 1, "error"}
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

    valid_native = File.read!(native)
    floating = String.replace(valid_native, "Ok(count as u64)", "Ok((count as f64) as u64)")
    refute floating == valid_native
    File.write!(native, floating)

    assert_raise CompileError, ~r/unsupported|reconstructed fallible/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(native, valid_native)

    wrong =
      String.replace(
        original,
        "closedTypeName, encode ⟨⟨#[7]⟩, ⟨#[1]⟩",
        "closedTypeName, encode ⟨⟨#[7]⟩, ⟨#[7]⟩"
      )

    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", rust)
    end

    File.write!(property, original)
    source = Path.join(workspace, "protocol/src/lib.rs")
    valid = File.read!(source)
    [before, function] = String.split(valid, "pub fn checked_write(", parts: 2)

    [function, rest] =
      String.split(function, "/// Applies request policy while owning an admitted", parts: 2)

    broken =
      function
      |> String.replace("    io_core::require_write(accepted);\n", "")
      |> String.replace(
        "    let result = match",
        "    io_core::require_write(accepted);\n    let result = match"
      )

    refute function == broken

    File.write!(
      source,
      before <>
        "pub fn checked_write(" <>
        broken <> "/// Applies request policy while owning an admitted" <> rest
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", rust)
    end

    File.write!(source, valid)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", rust).reports
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end

  defp project(tmp, name) do
    project = Path.join(tmp, name)
    File.mkdir_p!(Path.join(project, "CapturedFile"))
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
