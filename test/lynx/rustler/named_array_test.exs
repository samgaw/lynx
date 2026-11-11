defmodule Lynx.Rustler.NamedArrayTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/NamedArrayNif.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for named array NIF proofs")

  for sysroot <- [:default, :full_mir] do
    @tag sysroot: sysroot
    if sysroot == :full_mir and System.get_env("LYNX_FULL_MIR") != "1",
      do: @tag(skip: "set LYNX_FULL_MIR=1 for full-MIR standard-library checks")

    @tag :tmp_dir
    test "links named array and slice initializers through Rustler and Elixir laws (#{sysroot})",
         %{tmp_dir: tmp, sysroot: sysroot} do
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
          do: File.cp_r!(Path.join(@workspace, entry), Path.join(workspace, entry))

      native_name = "LynxRustFixture.NamedArrayNative#{Macro.camelize(Atom.to_string(sysroot))}"
      laws_name = "LynxRustFixture.NamedArrayLaws#{Macro.camelize(Atom.to_string(sysroot))}"
      native_source = Path.join(workspace, "nif/src/lib.rs")

      File.write!(
        native_source,
        String.replace(
          File.read!(native_source),
          "LynxRustFixture.Native",
          native_name
        )
      )

      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "NamedArrayNif"))
      packages = Path.join(@workspace, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        sysroot: sysroot,
        cargo: [features: ["named-slices"]],
        only: [wire_marker: 0, borrowed_wire_marker: 0],
        lean_project: project,
        module_prefix: "NamedArrayNif.Extraction",
        build_dir: Path.join(tmp, "build")
      ]

      discovered = Lynx.Rustler.prepare!(options)

      assert %{
               "wire_marker" =>
                 %{"name" => "wire_marker", "arity" => 0, "flags" => 0, "result" => "u32"} =
                   binding,
               "borrowed_wire_marker" =>
                 %{
                   "name" => "borrowed_wire_marker",
                   "arity" => 0,
                   "flags" => 0,
                   "result" => %{"option" => "u32"}
                 } = borrowed
             } = Map.new(discovered.bindings.bindings, &{&1["name"], &1})

      File.write!(
        Path.join(project, "NamedArrayNif/Properties.lean"),
        File.read!(@proof)
        |> String.replace("__FACADE__", binding["lean_name"])
        |> String.replace("__BORROWED_FACADE__", borrowed["lean_name"])
      )

      options =
        options ++
          [
            proof_modules: ["NamedArrayNif.Properties"],
            required_properties:
              Enum.map(
                ~w(core_spec composition facade borrowed_bytes core_borrowed borrowed_composition borrowed_facade),
                &("NamedArrayNif.Properties." <> &1)
              )
          ]

      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.all?(prepared.reports, &(&1.status == :ok))

      assert Enum.any?(
               prepared.verification.trusted_boundary,
               &String.starts_with?(&1, "Full-MIR")
             ) ==
               (sysroot == :full_mir)

      assert Enum.any?(
               prepared.verification.constants,
               &(&1["status"] == :extracted and String.ends_with?(&1["lean_name"], ".WIRE_MAGIC"))
             )

      library = Path.join(tmp, "native")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {name, arity, _} <- prepared.bindings.exports,
            do:
              "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      [{module, _}] =
        Code.compile_string("""
        defmodule #{native_name} do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(~c"#{library}",0)
          #{Enum.join(stubs, "\n")}
        end
        """)

      assert apply(module, :wire_marker, []) == 1_280_921_176
      assert apply(module, :borrowed_wire_marker, []) == 1_280_921_176
      law_source = Path.join(@workspace, "elixir/named_array_laws.ex")

      [{_, beam}] =
        law_source
        |> File.read!()
        |> String.replace("LynxRustFixture.NamedArrayNative", native_name)
        |> String.replace("LynxRustFixture.NamedArrayLaws", laws_name)
        |> Code.compile_string(law_source)

      export = Path.join(tmp, "named-array.export")
      reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
      guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

      for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
          do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

      assert Enum.all?(
               Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
               &(&1.status == :ok and &1.cached)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      source = Path.join(workspace, "core/src/protocol.rs")
      original = File.read!(source)

      for {before, replacement} <- [
            {"WIRE_MAGIC: [u8; 4] = [76, 89, 78, 88]", "WIRE_MAGIC: [u8; 4] = [76, 89, 78, 89]"},
            {~s(BORROWED_MAGIC: &[u8] = b"LYNX"), ~s(BORROWED_MAGIC: &[u8] = b"LYNY")},
            {~s(BORROWED_MAGIC: &[u8] = b"LYNX"), ~s(BORROWED_MAGIC: &[u8] = b"LYN")}
          ] do
        changed = String.replace(original, before, replacement)
        assert changed != original
        File.write!(source, changed)

        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rustler.prepare!(options)
        end
      end

      File.write!(source, original)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end
end
