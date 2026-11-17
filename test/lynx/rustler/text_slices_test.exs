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
        sysroot: :full_mir,
        mir: :promoted,
        root_attribute: if(@unpatched, do: "verify::start_from"),
        cargo: [features: ["text-slices"]],
        only: [
          slice_text: 3,
          split_text: 2,
          checked_split_text: 2,
          equal_text: 2,
          has_text_prefix: 2,
          consume_text_prefix: 2,
          parse_text_record: 3
        ],
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

      assert %{"arguments" => ["str", "str"], "result" => "bool", "flags" => 0} =
               bindings["equal_text"]

      assert %{
               "arguments" => ["str", "u8"],
               "flags" => 1,
               "result" => %{"option" => %{"tuple" => ["str", "str"]}}
             } = bindings["checked_split_text"]

      assert %{"arguments" => ["str", "str"], "result" => %{"option" => "str"}, "flags" => 0} =
               bindings["consume_text_prefix"]

      assert %{
               "arguments" => ["str", "u8", "u8"],
               "flags" => 1,
               "result" => %{"option" => %{"tuple" => ["str", "str", "str"]}}
             } = bindings["parse_text_record"]

      properties =
        File.read!(@proof)
        |> String.replace("experiment_analysis.core.slice.", "experiment_nif.core.slice.")
        |> String.replace("experiment_analysis.experiment_core", "experiment_nif.experiment_core")
        |> String.replace("experiment_analysis.", "experiment_nif.experiment_analysis.")

      File.write!(Path.join(project, "TextSlices/Properties.lean"), properties)

      record =
        File.read!(Path.join(Path.dirname(@proof), "TextRecord.lean"))
        |> String.replace("experiment_analysis.experiment_core", "experiment_nif.experiment_core")
        |> String.replace("experiment_analysis.", "experiment_nif.experiment_analysis.")

      File.write!(Path.join(project, "TextSlices/Record.lean"), record)

      adapter =
        File.read!(Path.join(Path.dirname(@proof), "TextSlicesAdapter.lean"))
        |> String.replace("__SLICE_NIF__", bindings["slice_text"]["lean_name"])
        |> String.replace("__CHECKED_NIF__", bindings["checked_split_text"]["lean_name"])
        |> String.replace("__EQUAL_NIF__", bindings["equal_text"]["lean_name"])
        |> String.replace("__PREFIX_NIF__", bindings["has_text_prefix"]["lean_name"])
        |> String.replace("__CONSUME_NIF__", bindings["consume_text_prefix"]["lean_name"])
        |> String.replace("__RECORD_NIF__", bindings["parse_text_record"]["lean_name"])

      File.write!(Path.join(project, "TextSlices/AdapterProperties.lean"), adapter)

      options =
        base ++
          [
            proof_modules: [
              "TextSlices.Properties",
              "TextSlices.Record",
              "TextSlices.AdapterProperties"
            ],
            required_properties:
              Enum.map(
                ~w(window_composition window_valid split_roundtrip split_rejected windows_unicode window_utf8 split_utf8 checked_implementation checked_consistent checked_rejected checked_utf8 checked_unicode text_equal_bytes text_equal_reflexive text_prefix_bytes text_prefix_reflexive consume_implementation consume_by_values consume_exact consume_utf8),
                &("TextSlices.Properties." <> &1)
              ) ++
                Enum.map(
                  ~w(tagged_composition tagged_exact tagged_returns tagged_sound record_sound record_accepts record_rejects_first record_rejects_second record_total record_unicode),
                  &("TextSlices.Record." <> &1)
                ) ++
                [
                  "TextSlices.AdapterProperties.window_encoding",
                  "TextSlices.AdapterProperties.equal_facade",
                  "TextSlices.AdapterProperties.prefix_facade",
                  "TextSlices.AdapterProperties.consume_facade",
                  "TextSlices.AdapterProperties.consume_encoding",
                  "TextSlices.AdapterProperties.record_facade",
                  "TextSlices.AdapterProperties.record_encoding",
                  "TextSlices.AdapterProperties.checked_facade_utf8"
                ]
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

      for {position, expected} <- [
            {0, {"", "aé🙂z"}},
            {1, {"a", "é🙂z"}},
            {2, nil},
            {3, {"aé", "🙂z"}},
            {8, {"aé🙂z", ""}},
            {9, nil}
          ],
          do: assert(apply(native, :checked_split_text, ["aé🙂z", position]) == expected)

      assert_raise ArgumentError, fn -> apply(native, :checked_split_text, [<<255>>, 0]) end

      assert apply(native, :equal_text, ["aé🙂z", "aé🙂z"])
      refute apply(native, :equal_text, ["é", "é"])
      refute apply(native, :equal_text, ["field", "field" <> <<0>>])
      assert_raise ArgumentError, fn -> apply(native, :equal_text, ["ok", <<255>>]) end

      for {text, prefix, expected} <- [
            {"aé🙂z", "aé", true},
            {"aé", "", true},
            {"a", "aé", false},
            {"é", "é", false}
          ],
          do: assert(apply(native, :has_text_prefix, [text, prefix]) == expected)

      assert_raise ArgumentError, fn -> apply(native, :has_text_prefix, ["ok", <<195>>]) end

      for {text, prefix, expected} <- [
            {"aé🙂z", "aé", "🙂z"},
            {"aé", "", "aé"},
            {"aé", "aé", ""},
            {"a", "aé", nil},
            {"é", "é", nil}
          ],
          do: assert(apply(native, :consume_text_prefix, [text, prefix]) == expected)

      assert_raise ArgumentError, fn -> apply(native, :consume_text_prefix, ["ok", <<195>>]) end

      assert apply(native, :parse_text_record, ["name:é|value:🙂tail", 2, 4]) == {"é", "🙂", "tail"}
      assert apply(native, :parse_text_record, ["name:|value:", 0, 0]) == {"", "", ""}

      for args <- [
            ["name:é|value:🙂", 1, 4],
            ["name:é|value:🙂", 2, 3],
            ["name:é|value:🙂", 2, 5],
            ["name:é|wrong:🙂", 2, 4]
          ],
          do: assert(apply(native, :parse_text_record, args) == nil)

      for args <- [[<<255>>, 2, 4], ["name:|value:", -1, 0], ["name:|value:", 0, 4_294_967_296]],
          do: assert_raise(ArgumentError, fn -> apply(native, :parse_text_record, args) end)

      cases = [
        {"Record",
         "#{native_name}.parse_text_record(\"name:é|value:🙂tail\",2,4) == {\"é\",\"🙂\",\"tail\"}"},
        {"RecordEmpty",
         "#{native_name}.parse_text_record(\"name:|value:\",0,0) == {\"\",\"\",\"\"}"},
        {"RecordNameBoundary", "#{native_name}.parse_text_record(\"name:é|value:🙂\",1,4) == nil"},
        {"RecordValueBoundary",
         "#{native_name}.parse_text_record(\"name:é|value:🙂\",2,3) == nil"},
        {"RecordTruncated", "#{native_name}.parse_text_record(\"name:é|value:🙂\",2,5) == nil"},
        {"RecordTag", "#{native_name}.parse_text_record(\"name:é|wrong:🙂\",2,4) == nil"},
        {"RecordMalformed",
         "try do #{native_name}.parse_text_record(<<255>>,2,4); false catch :error, :badarg -> true end"},
        {"Consume", "#{native_name}.consume_text_prefix(\"aé🙂z\",\"aé\") == \"🙂z\""},
        {"ConsumeEmpty", "#{native_name}.consume_text_prefix(\"aé\",\"\") == \"aé\""},
        {"ConsumeAll", "#{native_name}.consume_text_prefix(\"aé\",\"aé\") == \"\""},
        {"ConsumeLong", "#{native_name}.consume_text_prefix(\"a\",\"aé\") == nil"},
        {"ConsumeDifferent", "#{native_name}.consume_text_prefix(\"é\",\"é\") == nil"},
        {"ConsumeMalformed",
         "try do #{native_name}.consume_text_prefix(\"ok\",<<195>>); false catch :error, :badarg -> true end"},
        {"Prefix", "#{native_name}.has_text_prefix(\"aé🙂z\",\"aé\")"},
        {"EmptyPrefix", "#{native_name}.has_text_prefix(\"aé\",\"\")"},
        {"LongPrefix", "#{native_name}.has_text_prefix(\"a\",\"aé\") == false"},
        {"DifferentPrefix", "#{native_name}.has_text_prefix(\"é\",\"é\") == false"},
        {"MalformedPrefix",
         "try do #{native_name}.has_text_prefix(\"ok\",<<195>>); false catch :error, :badarg -> true end"},
        {"Equal", "#{native_name}.equal_text(\"aé🙂z\",\"aé🙂z\")"},
        {"Different", "#{native_name}.equal_text(\"é\",\"é\") == false"},
        {"Nul", "#{native_name}.equal_text(\"field\",<<102,105,101,108,100,0>>) == false"},
        {"Checked", "#{native_name}.checked_split_text(\"aé🙂z\",3) == {\"aé\",\"🙂z\"}"},
        {"CheckedInside", "#{native_name}.checked_split_text(\"aé🙂z\",2) == nil"},
        {"CheckedEnd", "#{native_name}.checked_split_text(\"aé🙂z\",8) == {\"aé🙂z\",\"\"}"},
        {"CheckedPastEnd", "#{native_name}.checked_split_text(\"aé🙂z\",9) == nil"},
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
          Elixir.#{native}.«split_text/2», Elixir.#{native}.«split_text:execution/2»,
          Elixir.#{native}.«parse_text_record/3», Elixir.#{native}.«parse_text_record:execution/3»,
          Elixir.#{native}.«consume_text_prefix/2», Elixir.#{native}.«consume_text_prefix:execution/2»,
          Elixir.#{native}.«has_text_prefix/2», Elixir.#{native}.«has_text_prefix:execution/2»,
          Elixir.#{native}.«equal_text/2», Elixir.#{native}.«equal_text:execution/2»,
          Elixir.#{native}.«checked_split_text/2», Elixir.#{native}.«checked_split_text:execution/2»]
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
