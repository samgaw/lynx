defmodule Lynx.Rustler.CapturedUnwindTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_CAPTURED_AENEAS_DIR for captured NIF proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    @tag nif_version: version
    test "proves composed cleanup through Rustler #{version} and Elixir laws", %{tmp_dir: tmp} do
      version = unquote(version)
      module = "LynxCapturedOwnership" <> String.replace(version, ".", "") <> "Fixture"
      native_module = String.to_atom("Elixir." <> module <> ".Native")
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for path <- ~w(Cargo.toml Cargo.lock base app nif elixir),
          do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

      native = Path.join(workspace, "nif/src/lib.rs")
      File.write!(native, String.replace(File.read!(native), "LynxOwnershipFixture", module))
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
      File.mkdir_p!(Path.join(project, "Captured"))
      File.mkdir_p!(Path.join(project, ".lake"))
      packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
      File.ln_s!(packages, Path.join(project, ".lake/packages"))

      options = [
        workspace: workspace,
        package: "ownership-nif",
        tools: @tools,
        root_attribute: "lynx::captured",
        owned_drops: :explicit,
        unwind: :captured,
        cargo: [features: ["captured-unwind"]],
        only: [captured_value: 2],
        lean_project: project,
        build_dir: Path.join(tmp, "build"),
        module_prefix: "Captured.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)

      assert [
               %{
                 "name" => "captured_value",
                 "arity" => 2,
                 "flags" => 1,
                 "captured_unwind" => true
               } = binding
             ] = prepared.bindings.bindings

      bad_audit =
        Map.update!(prepared.extraction.audit, :captured_unwind, fn records ->
          Enum.map(records, fn record ->
            if record.function_id == binding["definition_id"],
              do: update_in(record, [:captured_signature, "is_unsafe"], &(!&1)),
              else: record
          end)
        end)

      assert_raise ArgumentError, ~r/signature does not match its exit model/, fn ->
        Lynx.Rustler.Bindings.link!(prepared.bindings, bad_audit, prepared.extraction.translation)
      end

      properties =
        File.read!(Path.join(@fixture, "CapturedProperties.lean"))
        |> String.replace(
          "open Aeneas Aeneas.Std ownership_app",
          "open Aeneas Aeneas.Std ownership_nif ownership_nif.ownership_app"
        )

      properties =
        properties <>
          """

          namespace Captured.Properties
          theorem facade (value accepted : Bool) :
              #{binding["lean_name"]} value accepted = RustM.ok
                (if accepted then core.result.Result.Ok value else core.result.Result.Err ()) := by
            cases accepted <;> simp [#{binding["lean_name"]}, compose]
          end Captured.Properties
          """

      property = Path.join(project, "Captured/Properties.lean")
      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["Captured.Properties"],
            required_properties:
              ~w(Captured.Properties.checked_flip Captured.Properties.compose Captured.Properties.facade)
          ]

      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
      assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))
      File.mkdir_p!(Path.join(workspace, "priv"))
      File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
      stub = Path.join(workspace, "elixir/native.ex")

      File.write!(
        stub,
        File.read!(stub)
        |> String.replace("LynxOwnershipFixture", module)
        |> String.replace(
          "\nend\n",
          "\n  def captured_value(_value, _accepted), do: :erlang.nif_error(:not_loaded)\nend\n"
        )
      )

      Code.compile_file(stub)
      assert apply(native_module, :captured_value, [true, true]) == true
      assert apply(native_module, :captured_value, [false, true]) == false
      assert catch_error(apply(native_module, :captured_value, [true, false])) == :nif_panicked

      for args <- [[7, true], [true, 7]],
          do: assert_raise(ArgumentError, fn -> apply(native_module, :captured_value, args) end)

      laws = Path.join(workspace, "elixir/captured_laws.ex")
      File.write!(laws, String.replace(File.read!(laws), "LynxCapturedOwnershipFixture", module))
      [{_, beam}] = Code.compile_file(laws)
      export = Path.join(tmp, "captured-nif.export")
      reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

      assert reports |> Enum.flat_map(& &1.theorems) |> Enum.map(& &1.name) |> Enum.sort() ==
               ~w(panic_after_cleanup/0 preserves_false/0 preserves_true/0 rejects_first_argument/0 rejects_second_argument/0)

      assert Enum.all?(
               Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
               &(&1.status == :ok and &1.cached)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
      source = Path.join(workspace, "base/src/lib.rs")
      original = File.read!(source)
      File.write!(source, String.replace(original, "*self.0 = !*self.0;", "*self.0 = *self.0;"))

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(source, original)

      assert Enum.all?(
               Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
               &(&1.status == :ok)
             )
    end
  end
end
