defmodule Lynx.Rustler.VersionTest do
  use ExUnit.Case

  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "Rustler 0.38 uses the audited codecs with compiled metadata and actual workspace proofs",
       %{
         tmp_dir: tmp
       } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for file <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif elixir),
        do: File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))

    manifest = Path.join(workspace, "nif/Cargo.toml")
    File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=0.38.0"))
    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(
        File.read!(source),
        "LynxRustFixture.Native",
        "LynxRustFixture.Compat38Native"
      )
    )

    {output, status} =
      System.cmd(
        "cargo",
        [
          "update",
          "--manifest-path",
          Path.join(workspace, "Cargo.toml"),
          "-p",
          "rustler",
          "--precise",
          "0.38.0"
        ],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RustWorkspace"))

    for file <- ~w(Native BridgeTests),
        do:
          File.cp!(
            Path.join(@fixture, "proofs/RustWorkspace/#{file}.lean"),
            Path.join(project, "RustWorkspace/#{file}.lean")
          )

    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    prepared =
      Lynx.Rustler.prepare!(workspace, "experiment-nif",
        lean_project: project,
        build_dir: Path.join(tmp, "build"),
        module_prefix: "RustWorkspace.Facade",
        proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"],
        required_properties: ["RustWorkspace.Native.integer_facade"]
      )

    assert prepared.verification.rustler_version == "0.38.0"
    assert prepared.bindings.module == "Elixir.LynxRustFixture.Compat38Native"
    assert Enum.count(prepared.verification.guarantees, &(&1.kind == :nif_adapter)) == 10
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert "Rustler 0.38.0 wrapper, unsafe FFI, native code and BEAM NIF API" in prepared.verification.trusted_boundary

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libexperiment_nif.so"))
    native = Path.join(workspace, "elixir/native.ex")

    File.write!(
      native,
      String.replace(
        File.read!(native),
        "LynxRustFixture.Native",
        "LynxRustFixture.Compat38Native"
      )
    )

    assert {:ok, [LynxRustFixture.Compat38Native], _} =
             Kernel.ParallelCompiler.compile_to_path([native], tmp, return_diagnostics: true)

    module = LynxRustFixture.Compat38Native
    assert apply(module, :restore, [true])
    refute apply(module, :restore, [false])
    assert apply(module, :calculate, [21]) == 43
    assert apply(module, :echo_i8, [128]) == -128
    assert apply(module, :echo_u16, [65536]) == 0
    assert apply(module, :echo_u64, [18_446_744_073_709_551_615]) == 18_446_744_073_709_551_615
    assert catch_error(apply(module, :calculate, [9_223_372_036_854_775_807])) == :nif_panicked

    for {name, invalid} <- [
          restore: 0,
          echo_i8: 2_147_483_648,
          echo_u64: -1,
          echo_u64: 18_446_744_073_709_551_616
        ] do
      assert_raise ArgumentError, fn -> apply(module, name, [invalid]) end
    end

    laws = Path.join(workspace, "elixir/laws.ex")

    File.write!(
      laws,
      File.read!(laws)
      |> String.replace("LynxRustFixture.Native", "LynxRustFixture.Compat38Native")
      |> String.replace("LynxRustFixture.Laws", "LynxRustFixture.Compat38Laws")
    )

    [{LynxRustFixture.Compat38Laws, beam}] = Code.compile_file(laws)

    reports =
      Lynx.Laws.verify([beam],
        native:
          {Lynx.Rustler,
           workspace: workspace,
           package: "experiment-nif",
           lean_project: project,
           build_dir: Path.join(tmp, "build"),
           module_prefix: "RustWorkspace.Facade",
           proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"],
           required_properties: ["RustWorkspace.Native.integer_facade"]}
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

    assert Enum.any?(reports, fn report ->
             Enum.any?(Map.get(report, :guarantees, []), &(&1.kind == :elixir_law))
           end)
  end
end
