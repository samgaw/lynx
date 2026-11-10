defmodule Lynx.Rustler.ExplicitOwnershipTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for Rustler ownership proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "proves actual cross-crate destruction through Rustler #{version} and Elixir laws", %{
      tmp_dir: tmp
    } do
      version = unquote(version)
      module = "LynxOwnership" <> String.replace(version, ".", "") <> "Fixture"
      native_module = String.to_atom("Elixir." <> module <> ".Native")
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for path <- ~w(Cargo.toml Cargo.lock base app nif elixir),
          do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

      native = Path.join(workspace, "nif/src/lib.rs")
      File.write!(native, String.replace(File.read!(native), "LynxOwnershipFixture", module))

      for file <- ~w(native.ex laws.ex) do
        path = Path.join(workspace, "elixir/" <> file)
        File.write!(path, String.replace(File.read!(path), "LynxOwnershipFixture", module))
      end

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))

      {output, status} =
        System.cmd(
          "cargo",
          [
            "update",
            "--offline",
            "--manifest-path",
            manifest,
            "-p",
            "rustler",
            "--precise",
            version
          ],
          stderr_to_stdout: true
        )

      assert status == 0, output
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "Ownership"))
      File.mkdir_p!(Path.join(project, "OwnershipNif"))
      packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))

      options = [
        workspace: workspace,
        package: "ownership-nif",
        tools: @tools,
        root_attribute: "verify::start_from",
        owned_drops: :explicit,
        lean_project: project,
        build_dir: Path.join(tmp, "build"),
        module_prefix: "OwnershipNif.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)

      assert [
               %{"name" => "checked_code", "flags" => 1} = checked,
               %{"name" => "scalar_code", "flags" => 0} = scalar
             ] =
               Enum.sort_by(prepared.bindings.bindings, & &1["name"])

      properties =
        File.read!(Path.join(@fixture, "Properties.lean"))
        |> String.replace(
          "public import Ownership.Funs",
          "public import OwnershipNif.Extraction.Funs"
        )
        |> String.replace(
          "open Aeneas Aeneas.Std ownership_app",
          "open Aeneas Aeneas.Std ownership_nif ownership_nif.ownership_app"
        )

      property = Path.join(project, "OwnershipNif/Internal.lean")
      File.write!(property, properties)

      facade =
        File.read!(Path.join(@fixture, "NifProperties.lean"))
        |> String.replace("__CHECKED__", checked["lean_name"])
        |> String.replace("__SCALAR__", scalar["lean_name"])

      File.write!(Path.join(project, "OwnershipNif/Properties.lean"), facade)

      options =
        options ++
          [
            proof_modules: ["OwnershipNif.Internal", "OwnershipNif.Properties"],
            required_properties:
              Enum.map(
                ~w(consume_contract scalar_finishes run_panics run_returns),
                &("Ownership.Properties." <> &1)
              ) ++
                Enum.map(~w(checked checked_panics scalar), &("OwnershipNif.Properties." <> &1))
          ]

      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.count(prepared.verification.guarantees, &(&1.kind == :nif_adapter)) == 2
      assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
      refute prepared.verification.compiler_primitives == []
      assert prepared.verification.structural_drops == []
      File.mkdir_p!(Path.join(workspace, "priv"))
      File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
      Code.compile_file(Path.join(workspace, "elixir/native.ex"))
      assert apply(native_module, :checked_code, [8])
      assert apply(native_module, :scalar_code, [7])
      assert catch_error(apply(native_module, :checked_code, [7])) == :nif_panicked

      for bad <- [-1, 18_446_744_073_709_551_616, :invalid] do
        assert_raise ArgumentError, fn ->
          apply(native_module, :checked_code, [bad])
        end
      end

      [{_, beam}] = Code.compile_file(Path.join(workspace, "elixir/laws.ex"))
      export = Path.join(tmp, "ownership-nif.export")
      assert_verified(Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export))

      assert Enum.all?(
               Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
               &(&1.status == :ok and &1.cached)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      for extra <- [
            "private axiom ownershipTrust : False",
            "private theorem unfinishedOwnership : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      File.write!(property, properties)
      core = Path.join(workspace, "base/src/lib.rs")
      original = File.read!(core)
      File.write!(core, String.replace(original, "self.code != 7", "self.code != 8"))

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(core, original)
      assert_verified(Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}))
    end
  end

  @tag :tmp_dir
  @tag :unwind_admission
  test "rejects actual double-panic cleanup, erased overflow cleanup and owned NIF results", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    options = [
      workspace: workspace,
      package: "ownership-nif",
      tools: @tools,
      root_attribute: "verify::start_from",
      owned_drops: :explicit,
      lean_project: Path.join(tmp, "proofs"),
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Rejected.Extraction"
    ]

    app = Path.join(workspace, "app/src/lib.rs")
    original = File.read!(app)
    call = "ownership_base::consume(ownership_base::Audit { code });"

    for {replacement, reason} <- [
          {"let _pending = ownership_base::Audit { code: 7 }; " <> call,
           ~r/observable unwind cleanup/},
          {"let value = ownership_base::Audit { code: 7 }; let _sum = code + 1; ownership_base::consume(value);",
           ~r/reconstructed fallible operations with owned locals/}
        ] do
      changed = String.replace(original, call, replacement)
      refute changed == original
      File.write!(app, changed)
      assert_raise CompileError, reason, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(app, original)
    native = Path.join(workspace, "nif/src/lib.rs")

    source =
      File.read!(native)
      |> String.replace(
        "fn checked(code: u64) -> bool {",
        "fn checked(code: u64) -> OwnedOutput {"
      )
      |> String.replace(
        "ownership_app::run(code);\n    true",
        "ownership_app::run(code);\n    OwnedOutput(code)"
      )

    File.write!(
      native,
      source <>
        """

        #[derive(rustler::NifTuple)]
        struct OwnedOutput(u64);
        impl Drop for OwnedOutput {
            fn drop(&mut self) { assert!(self.0 != 7); }
        }
        """
    )

    assert_raise ArgumentError, ~r/destructor-free value codecs/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end

  defp assert_verified(reports) do
    assert reports != []

    for report <- reports,
        do: assert(report.status == :ok, inspect(report, pretty: true, limit: :infinity))
  end
end
