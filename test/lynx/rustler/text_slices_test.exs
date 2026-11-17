defmodule Lynx.Rustler.TextSlicesTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/TextSlices.lean", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for text slicing NIF proofs")

  for version <- ["0.38.0", "0.39.0"] do
    @tag :tmp_dir
    test "composes character-safe protocol fields through Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      native_name = "LynxTextSlices#{String.replace(version, ".", "")}Fixture.Native"
      native = String.to_atom("Elixir." <> native_name)
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for entry <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@workspace, entry), Path.join(workspace, entry))

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output
      source = Path.join(workspace, "nif/src/lib.rs")

      rust =
        File.read!(source)
        |> String.replace("LynxRustFixture.Native", native_name)
        |> String.replace("LynxRustFixture.BinaryNative", native_name)

      rust =
        if @unpatched do
          "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
            Regex.replace(~r/(^#\[rustler::nif[^\n]*\]\n)/m, rust, "\\1#[verify::start_from]\n")
        else
          rust
        end

      File.write!(source, rust)
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "TextSlices"))
      File.mkdir_p!(Path.join(project, ".lake"))

      File.ln_s!(
        Path.join(@workspace, "proofs/.lake/packages"),
        Path.join(project, ".lake/packages")
      )

      base = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        root_attribute: if(@unpatched, do: "verify::start_from"),
        cargo: [features: ["text-slices"]],
        only: [slice_text: 3, split_text: 2],
        lean_project: project,
        module_prefix: "TextSlices.Extraction",
        build_dir: Path.join(tmp, "build")
      ]

      discovered = Lynx.Rustler.prepare!(base)
      bindings = Map.new(discovered.bindings.bindings, &{&1["name"], &1})

      assert %{"arguments" => ["str", "u8", "u8"], "result" => %{"option" => "str"}, "flags" => 1} =
               bindings["slice_text"]

      assert %{
               "arguments" => ["str", "u8"],
               "result" => %{"option" => %{"tuple" => ["str", "str"]}}
             } = bindings["split_text"]

      properties =
        File.read!(@proof)
        |> String.replace("experiment_analysis.experiment_core", "experiment_nif.experiment_core")
        |> String.replace("experiment_analysis.", "experiment_nif.experiment_analysis.")

      File.write!(Path.join(project, "TextSlices/Properties.lean"), properties)

      adapter =
        File.read!(Path.join(Path.dirname(@proof), "TextSlicesAdapter.lean"))
        |> String.replace("__SLICE_NIF__", bindings["slice_text"]["lean_name"])

      File.write!(Path.join(project, "TextSlices/AdapterProperties.lean"), adapter)

      options =
        base ++
          [
            proof_modules: ["TextSlices.Properties", "TextSlices.AdapterProperties"],
            required_properties:
              Enum.map(
                ~w(window_composition window_valid split_roundtrip split_rejected windows_unicode window_utf8 split_utf8),
                &("TextSlices.Properties." <> &1)
              ) ++ ["TextSlices.AdapterProperties.window_encoding"]
          ]

      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.all?(prepared.reports, &(&1.status == :ok))
      library = Path.join(tmp, "native")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {name, arity, _} <- prepared.bindings.exports,
            do:
              "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      Code.compile_string("""
      defmodule #{native_name} do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
        #{Enum.join(stubs, "\n")}
      end
      """)

      for {start, stop, expected} <- [
            {1, 3, "é"},
            {3, 7, "🙂"},
            {2, 2, nil},
            {1, 1, ""},
            {8, 8, ""},
            {9, 9, nil},
            {7, 3, nil}
          ],
          do: assert(apply(native, :slice_text, ["aé🙂z", start, stop]) == expected)

      assert apply(native, :split_text, ["aé🙂z", 3]) == {"aé", "🙂z"}
      assert apply(native, :slice_text, ["aé🙂z", 257, 259]) == "é"
      assert apply(native, :split_text, ["aé🙂z", 2]) == nil

      for args <- [[<<255>>, 0, 0], [[97], 0, 0], ["é", -1, 0], ["é", 0, 4_294_967_296]],
          do: assert_raise(ArgumentError, fn -> apply(native, :slice_text, args) end)

      cases = [
        {"Narrowing", "#{native_name}.slice_text(\"aé🙂z\",257,259) == \"é\""},
        {"Window", "#{native_name}.slice_text(\"aé🙂z\",1,3) == \"é\""},
        {"Inside", "#{native_name}.slice_text(\"aé🙂z\",2,2) == nil"},
        {"Split", "#{native_name}.split_text(\"aé🙂z\",3) == {\"aé\",\"🙂z\"}"},
        {"RejectedSplit", "#{native_name}.split_text(\"aé🙂z\",2) == nil"},
        {"Malformed",
         "try do #{native_name}.slice_text(<<255>>,0,0); false catch :error, :badarg -> true end"},
        {"Offset",
         "try do #{native_name}.slice_text(\"é\",0,4294967296); false catch :error, :badarg -> true end"}
      ]

      beams =
        for {name, expression} <- cases do
          [{_, beam}] = Code.compile_string(law(native_name, name, expression))
          beam
        end

      export = Path.join(tmp, "text-slices.export")
      reports = Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}, export: export)
      assert [] == for(r <- reports, r.status != :ok, do: {r.module, r.diagnostics})
      guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

      for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
          do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

      assert Enum.all?(
               Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}),
               &(&1.status == :ok and &1.cached)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
    end
  end

  defp law(native, name, expression) do
    """
    defmodule #{String.trim_trailing(native, ".Native")}.#{name} do
      @compile :debug_info
      use Lynx.Laws
      law slicing,
        expects: (#{expression}),
        proof: ~LEAN\"\"\"
        simp only [Lynx.apply,«slicing:ensures/0»,
          Elixir.#{native}.«slice_text/3», Elixir.#{native}.«slice_text:execution/3»,
          Elixir.#{native}.«split_text/2», Elixir.#{native}.«split_text:execution/2»]
        cbv
        all_goals
          rcases System.Platform.numBits_eq with bits | bits
          all_goals
            simp only [System.Platform.numBits] at bits
            simp only [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits,
              Aeneas.Std.Isize.max, Aeneas.Std.Isize.numBits,
              Aeneas.Std.UScalarTy.numBits, Aeneas.Std.IScalarTy.numBits, bits]
            cbv
        \"\"\"
    end
    """
  end
end
