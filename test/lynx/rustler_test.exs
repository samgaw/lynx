defmodule Lynx.RustlerTest do
  use ExUnit.Case

  @fixture Path.expand("../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "proves Elixir laws using the extracted Rustler facade", %{tmp_dir: tmp_dir} do
    {output, status} =
      System.cmd(
        "rustup",
        [
          "run",
          "nightly-2026-09-17",
          "cargo",
          "test",
          "--locked",
          "--manifest-path",
          Path.join(@fixture, "Cargo.toml"),
          "-p",
          "experiment-nif",
          "--lib"
        ],
        stderr_to_stdout: true
      )

    assert status == 0, output

    project = Path.join(@fixture, "proofs")

    prepared =
      Lynx.Rustler.prepare!(@fixture, "experiment-nif",
        lean_project: project,
        module_prefix: "RustWorkspace.Facade",
        proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"]
      )

    repeated =
      Lynx.Rustler.prepare!(@fixture, "experiment-nif",
        lean_project: project,
        module_prefix: "RustWorkspace.Facade",
        proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"]
      )

    assert repeated.extraction.fingerprint == prepared.extraction.fingerprint
    assert repeated.external.fingerprint == prepared.external.fingerprint

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :rust_implementation &&
               evidence.theorem == "RustWorkspace.Native.double_spec" &&
               evidence.status == :verified && String.ends_with?(evidence.file, "core/src/lib.rs")
           end)

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract &&
               evidence.theorem == "RustWorkspace.Native.integer_composition" &&
               "RustWorkspace.Native.double_spec" in evidence.contracts_used
           end)

    assert Enum.count(prepared.verification.guarantees, &(&1.kind == :nif_adapter)) == 10

    refute Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :rust_implementation &&
               String.ends_with?(evidence.rust_name, "echo_u64")
           end)

    assert Enum.all?(repeated.reports, &(&1.status == :ok && &1.cached))
    File.mkdir_p!(Path.join(@fixture, "priv"))
    File.cp!(prepared.library, Path.join(@fixture, "priv/libexperiment_nif.so"))

    compiled = Lynx.Rustler.Metadata.inspect!(prepared.library)
    expanded_file = prepared.expanded
    discovered = Lynx.Rustler.Metadata.bindings!(expanded_file, compiled)

    exports =
      ~w(calculate echo_i16 echo_i32 echo_i8 echo_u16 echo_u32 echo_u64 echo_u8 negate restore)

    assert compiled.exports == Enum.map(exports, &{&1, 1, if(&1 == "restore", do: 1, else: 0)})
    assert discovered.module == "Elixir.LynxRustFixture.Native"

    changed =
      File.read!(expanded_file)
      |> String.replace("SchedulerFlags::DirtyCpu", "SchedulerFlags::Normal")

    refute changed == File.read!(expanded_file)
    tampered = Path.join(tmp_dir, "wrong-scheduler.rs")
    File.write!(tampered, changed)

    assert_raise RuntimeError, ~r/do not match the compiled NIF table/, fn ->
      Lynx.Rustler.Metadata.bindings!(tampered, compiled)
    end

    assert {:ok, [LynxRustFixture.Native], _} =
             Kernel.ParallelCompiler.compile_to_path(
               [Path.join(@fixture, "elixir/native.ex")],
               tmp_dir,
               return_diagnostics: true
             )

    assert apply(LynxRustFixture.Native, :restore, [true]) == true
    assert apply(LynxRustFixture.Native, :restore, [false]) == false
    assert apply(LynxRustFixture.Native, :restored, [true]) == true
    assert apply(LynxRustFixture.Native, :restored_remotely, [false]) == false
    assert apply(LynxRustFixture.Native, :restored_by_fun, [true]) == true
    assert apply(LynxRustFixture.Native, :negate, [true]) == false
    assert apply(LynxRustFixture.Native, :negate, [false]) == true

    assert Enum.sort(apply(LynxRustFixture.Native, :module_info, [:nifs])) ==
             Enum.map(exports, &{String.to_atom(&1), 1})

    assert apply(LynxRustFixture.Native, :calculate, [21]) == 43

    assert apply(LynxRustFixture.Native, :calculate, [-4_611_686_018_427_387_904]) ==
             -9_223_372_036_854_775_807

    assert apply(LynxRustFixture.Native, :calculate, [4_611_686_018_427_387_903]) ==
             9_223_372_036_854_775_807

    for input <- [
          -9_223_372_036_854_775_808,
          4_611_686_018_427_387_904,
          9_223_372_036_854_775_807
        ] do
      assert catch_error(apply(LynxRustFixture.Native, :calculate, [input])) == :nif_panicked
    end

    for input <- [-9_223_372_036_854_775_809, 9_223_372_036_854_775_808, true, 1.0] do
      assert_raise ArgumentError, fn -> apply(LynxRustFixture.Native, :calculate, [input]) end
    end

    for {name, pairs} <- [
          echo_i8: [{-129, 127}, {128, -128}, {2_147_483_647, -1}],
          echo_i16: [{-32769, 32767}, {32768, -32768}],
          echo_i32: [{-2_147_483_648, -2_147_483_648}, {2_147_483_647, 2_147_483_647}],
          echo_u8: [{256, 0}, {4_294_967_295, 255}],
          echo_u16: [{65536, 0}, {4_294_967_295, 65535}],
          echo_u32: [{0, 0}, {4_294_967_295, 4_294_967_295}],
          echo_u64: [{0, 0}, {18_446_744_073_709_551_615, 18_446_744_073_709_551_615}]
        ],
        {input, expected} <- pairs do
      assert apply(LynxRustFixture.Native, name, [input]) == expected
    end

    for name <- [:echo_i8, :echo_i16, :echo_i32], input <- [-2_147_483_649, 2_147_483_648] do
      assert_raise ArgumentError, fn -> apply(LynxRustFixture.Native, name, [input]) end
    end

    for name <- [:echo_u8, :echo_u16, :echo_u32], input <- [-1, 4_294_967_296] do
      assert_raise ArgumentError, fn -> apply(LynxRustFixture.Native, name, [input]) end
    end

    assert_raise ArgumentError, fn ->
      apply(LynxRustFixture.Native, :echo_u64, [18_446_744_073_709_551_616])
    end

    assert_raise ArgumentError, fn -> apply(LynxRustFixture.Native, :restore, [0]) end

    [{module, beam}] = Code.compile_file(Path.join(@fixture, "elixir/laws.ex"))
    assert module == LynxRustFixture.Laws

    external = prepared.external
    assert Enum.sort(Enum.map(prepared.bindings.bindings, & &1["name"])) == exports

    reports =
      Lynx.Laws.verify([beam],
        native:
          {Lynx.Rustler,
           workspace: @fixture,
           package: "experiment-nif",
           lean_project: project,
           module_prefix: "RustWorkspace.Facade",
           proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"]}
      )

    assert Enum.any?(reports, fn report ->
             Enum.any?(
               Map.get(report, :guarantees, []),
               &(&1.kind == :elixir_law && &1.status == :verified)
             )
           end)

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(reports, pretty: true, limit: :infinity)

    assert Enum.any?(reports, &(&1.module == "Elixir.LynxRustFixture.Laws.laws"))
    cached = Lynx.Laws.verify([beam], externals: [external], lean_project: project)
    assert Enum.all?(cached, &(&1.status == :ok && &1.cached))

    [{_, mixed_beam}] = Code.compile_file(Path.join(@fixture, "elixir/mixed_laws.ex"))
    mixed = Lynx.Laws.verify([mixed_beam], externals: [external], lean_project: project)
    assert Enum.all?(mixed, &(&1.status == :ok)), inspect(mixed, pretty: true, limit: :infinity)
    assert Enum.any?(mixed, &(&1.module == "Elixir.LynxRustFixture.Native"))
    mixed_cached = Lynx.Laws.verify([mixed_beam], externals: [external], lean_project: project)
    assert Enum.all?(mixed_cached, &(&1.status == :ok && &1.cached))

    [{_, unverified_helper}] =
      Code.compile_string("""
      defmodule LynxRustFixture.UnverifiedHelperLaws do
        @compile :debug_info
        use Lynx.Laws
        law missing, expects: LynxRustFixture.Native.unverified_echo(1) == 1, proof: ~LEAN"rfl"
      end
      """)

    selected = %{
      external
      | bindings: Enum.reject(external.bindings, &(&1 == {LynxRustFixture.Native, :echo_i8, 1}))
    }

    assert_raise CompileError, ~r/unregistered external implementation.*echo_i8\/1/, fn ->
      Lynx.Laws.verify([unverified_helper], externals: [selected], lean_project: project)
    end

    Code.compile_file(Path.join(@fixture, "elixir/case_laws.ex"))
    [test] = apply(LynxRustFixture.CaseLaws, :__ex_unit__, []).tests
    assert apply(LynxRustFixture.CaseLaws, test.name, [%{}]) == :ok

    export = Path.join(tmp_dir, "native.export")

    reports =
      Lynx.Laws.verify([beam, mixed_beam],
        externals: [external],
        lean_project: project,
        export: export
      )

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(reports, pretty: true, limit: :infinity)

    # This is our generated export. macOS cannot run Lake's Linux bwrap sandbox.
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end

  @tag :tmp_dir
  test "selects verified bindings while validating every compiled export", %{tmp_dir: tmp} do
    project = Path.join(@fixture, "proofs")

    prepared =
      Lynx.Rustler.prepare!(@fixture, "experiment-nif",
        lean_project: project,
        module_prefix: "RustWorkspace.Facade",
        proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"],
        cargo: [features: ["unsupported-float"]],
        only: [restore: 1, negate: 1, calculate: 1]
      )

    assert Enum.sort(Enum.map(prepared.bindings.bindings, & &1["name"])) ==
             ~w(calculate negate restore)

    assert Enum.count(prepared.verification.guarantees, &(&1.kind == :nif_adapter)) == 3
    assert length(prepared.verification.unverified_nif_exports) == 8

    assert Enum.any?(
             prepared.verification.unverified_nif_exports,
             &(&1.function == "echo_float" && &1.status == :unverified)
           )

    compiled = Lynx.Rustler.Metadata.inspect!(prepared.library)
    assert {"echo_float", 1, 0} in compiled.exports

    assert_raise RuntimeError, ~r/unsupported Rustler parameter or return type/, fn ->
      Lynx.Rustler.Metadata.bindings!(prepared.expanded, compiled)
    end

    for selection <- [[echo_float: 1], [echo_float: 1, restore: 1]] do
      assert_raise RuntimeError, ~r/unsupported Rustler parameter or return type/, fn ->
        Lynx.Rustler.Metadata.bindings!(prepared.expanded, compiled, selection)
      end
    end

    for selection <- [[], [missing: 1], [restore: 2], [restore: 1, restore: 1]] do
      assert_raise ArgumentError, fn ->
        Lynx.Rustler.Metadata.bindings!(prepared.expanded, compiled, selection)
      end
    end

    # A modification to an unselected export must still invalidate discovery.
    tampered = Path.join(tmp, "unselected-name.rs")
    source = File.read!(prepared.expanded)
    changed = String.replace(source, ~S("echo_float\u{0}"), ~S("other_float\u{0}"))
    refute source == changed
    File.write!(tampered, changed)

    assert_raise RuntimeError, ~r/do not match the compiled NIF table/, fn ->
      Lynx.Rustler.Metadata.bindings!(tampered, compiled, restore: 1)
    end

    [{_, beam}] =
      Path.join(@fixture, "elixir/laws.ex")
      |> File.read!()
      |> String.replace(
        "defmodule LynxRustFixture.Laws do",
        "defmodule LynxRustFixture.SelectedLaws do"
      )
      |> Code.compile_string()

    reports = Lynx.Laws.verify([beam], externals: [prepared.external], lean_project: project)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

    [{_, missing}] =
      Code.compile_string("""
      defmodule LynxRustFixture.UnselectedLaws do
        @compile :debug_info
        use Lynx.Laws
        law unselected, expects: LynxRustFixture.Native.echo_i8(1) == 1, proof: ~LEAN"rfl"
      end
      """)

    assert_raise CompileError, ~r/unregistered external implementation/, fn ->
      Lynx.Laws.verify([missing], externals: [prepared.external], lean_project: project)
    end
  end

  @tag :tmp_dir
  test "rejects aborting builds instead of modelling their panics as exceptions", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for file <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated) do
      File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))
    end

    manifest = Path.join(workspace, "Cargo.toml")
    File.write!(manifest, File.read!(manifest) <> "\n[profile.dev]\npanic = \"abort\"\n")

    assert_raise RuntimeError, ~r/Rustler relies on unwinding/, fn ->
      Lynx.Rustler.prepare!(workspace, "experiment-nif",
        lean_project: Path.join(@fixture, "proofs"),
        module_prefix: "RustWorkspace.Aborting",
        build_dir: Path.join(tmp, "build")
      )
    end
  end
end
