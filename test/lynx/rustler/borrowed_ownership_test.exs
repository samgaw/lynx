defmodule Lynx.Rustler.BorrowedOwnershipTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for borrowed NIF proofs")

  for version <- ["0.39.0", "0.38.0"] do
    @tag :tmp_dir
    test "observes actual borrowed guard cleanup through Rustler #{version} and Elixir laws", %{
      tmp_dir: tmp
    } do
      version = unquote(version)
      module = "LynxBorrowedOwnership" <> String.replace(version, ".", "") <> "Fixture"
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
      File.mkdir_p!(Path.join(project, "Borrowed"))
      File.mkdir_p!(Path.join(project, ".lake"))
      packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
      File.ln_s!(packages, Path.join(project, ".lake/packages"))

      options = [
        workspace: workspace,
        package: "ownership-nif",
        tools: @tools,
        root_attribute: "verify::start_from",
        owned_drops: :explicit,
        cargo: [features: ["borrowed-guard"]],
        only: [borrowed_flip: 1],
        lean_project: project,
        build_dir: Path.join(tmp, "build"),
        module_prefix: "Borrowed.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)
      assert [%{"name" => "borrowed_flip", "flags" => 0} = binding] = prepared.bindings.bindings

      properties =
        File.read!(Path.join(@fixture, "BorrowedProperties.lean"))
        |> String.replace(
          "open Aeneas Aeneas.Std ownership_app",
          "open Aeneas Aeneas.Std ownership_nif ownership_nif.ownership_app"
        )

      properties =
        properties <>
          """

          namespace Borrowed.Properties
          theorem facade (value : Bool) : #{binding["lean_name"]} value = RustM.ok (!value) := by
            simp [#{binding["lean_name"]}, scoped_flip]
          end Borrowed.Properties
          """

      property = Path.join(project, "Borrowed/Properties.lean")
      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["Borrowed.Properties"],
            required_properties:
              Enum.map(~w(flip_contract scoped_flip facade), &("Borrowed.Properties." <> &1))
          ]

      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
      assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))
      assert [%{function_id: _}] = prepared.extraction.explicit_ownership.reference_copies
      File.mkdir_p!(Path.join(workspace, "priv"))
      File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
      stub = Path.join(workspace, "elixir/native.ex")

      File.write!(
        stub,
        File.read!(stub)
        |> String.replace("LynxOwnershipFixture", module)
        |> String.replace(
          "\nend\n",
          "\n  def borrowed_flip(_value), do: :erlang.nif_error(:not_loaded)\nend\n"
        )
      )

      Code.compile_file(stub)
      assert apply(native_module, :borrowed_flip, [true]) == false
      assert apply(native_module, :borrowed_flip, [false]) == true
      assert_raise ArgumentError, fn -> apply(native_module, :borrowed_flip, [7]) end
      laws = Path.join(workspace, "elixir/borrowed_laws.ex")
      File.write!(laws, String.replace(File.read!(laws), "LynxBorrowedOwnershipFixture", module))
      [{_, beam}] = Code.compile_file(laws)
      export = Path.join(tmp, "borrowed-nif.export")
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
            "private axiom borrowedNifTrust : False",
            "private theorem unfinishedBorrowNif : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      File.write!(property, properties)
      source = Path.join(workspace, "base/src/lib.rs")
      original = File.read!(source)
      File.write!(source, String.replace(original, "*self.0 = !*self.0;", "*self.0 = *self.0;"))

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(source, original)
      assert_verified(Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}))
    end
  end

  defp assert_verified(reports) do
    assert reports != []

    for report <- reports,
        do: assert(report.status == :ok, inspect(report, pretty: true, limit: :infinity))
  end
end
