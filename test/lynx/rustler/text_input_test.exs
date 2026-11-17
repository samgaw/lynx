defmodule Lynx.Rustler.TextInputTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/TextInputProperties.lean", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for owned text NIF proofs")

  for version <- ["0.38.0", "0.39.0"] do
    @tag :tmp_dir
    test "proves typed String decoding and workspace text operations with Rustler #{version}", %{
      tmp_dir: tmp
    } do
      version = unquote(version)
      native_module = "LynxTextInput#{String.replace(version, ".", "")}Fixture.Native"
      module = String.to_atom("Elixir." <> native_module)
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for item <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@workspace, item), Path.join(workspace, item))

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

      native_source =
        File.read!(source)
        |> String.replace("LynxRustFixture.Native", native_module)
        |> String.replace("LynxRustFixture.BinaryNative", native_module)

      native_source =
        if @unpatched do
          "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
            Regex.replace(
              ~r/(^#\[rustler::nif[^\n]*\]\n)/m,
              native_source,
              "\\1#[verify::start_from]\n"
            )
        else
          native_source
        end

      File.write!(source, native_source)

      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "TextInput"))
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
        cargo: [features: ["text-input"]],
        only: [decorate_text: 2, owned_nonempty: 1, echo_text_option: 1],
        lean_project: project,
        module_prefix: "TextInput.Extraction",
        build_dir: Path.join(tmp, "build")
      ]

      discovered = Lynx.Rustler.prepare!(base)

      bindings = Map.new(discovered.bindings.bindings, &{&1["name"], &1})
      assert bindings["decorate_text"]["arguments"] == ["string", "bool"]
      assert bindings["decorate_text"]["flags"] == 1

      assert bindings["echo_text_option"]["arguments"] == [
               %{"tuple" => [%{"option" => "string"}, "bool"]}
             ]

      assert bindings["owned_nonempty"]["result"] == "bool"

      properties =
        File.read!(@proof)
        |> String.replace("__DECORATE__", bindings["decorate_text"]["lean_name"])
        |> String.replace("__NONEMPTY__", bindings["owned_nonempty"]["lean_name"])

      File.write!(Path.join(project, "TextInput/Properties.lean"), properties)

      required =
        Enum.map(
          ~w(unmarked marked exceeds_spec nonempty_spec nonempty_unicode empty_text facade_marked facade_unmarked facade_nonempty),
          &("TextInput.Properties." <> &1)
        )

      options = base ++ [proof_modules: ["TextInput.Properties"], required_properties: required]
      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.all?(prepared.reports, &(&1.status == :ok))

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "String Encoder model")
             )

      assert Enum.any?(prepared.trusted_boundary, &String.contains?(&1, "String Encoder model"))

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "String Decoder model")
             )

      library = Path.join(tmp, "native")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {name, arity, _} <- prepared.bindings.exports,
            do:
              "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      native = Path.join(tmp, "native.ex")

      File.write!(native, """
      defmodule #{native_module} do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}",0)
        #{Enum.join(stubs, "\n")}
      end
      """)

      assert {:ok, [^module], _} =
               Lynx.Rustler.NifFixture.compile!(native, tmp, module)

      {calibration, 0} =
        System.cmd(
          "elixir",
          [
            "-e",
            """
            Code.compile_file(#{inspect(native)})
            values = [#{native_module}.decorate_text("hé",true),
              #{native_module}.decorate_text("hé",false),
              #{native_module}.decorate_text(<<0>>,true),
              #{native_module}.echo_text_option({nil,true}),
              #{native_module}.echo_text_option({"hé",false}),
              #{native_module}.owned_nonempty(""),
              #{native_module}.owned_nonempty("hé")]
            IO.inspect(values)
            for thunk <- [fn -> #{native_module}.decorate_text(<<195,40>>,true) end,
              fn -> #{native_module}.decorate_text(<<240,159>>,true) end,
              fn -> #{native_module}.decorate_text([97],true) end,
              fn -> #{native_module}.decorate_text(<<1::1>>,true) end,
              fn -> #{native_module}.decorate_text("hé",0) end,
              fn -> #{native_module}.echo_text_option({<<195,40>>,true}) end] do
              try do thunk.(); raise "expected badarg" catch :error, :badarg -> IO.puts("badarg confirmed") end
            end
            """
          ],
          cd: tmp,
          env: [{"ERL_FLAGS", "+S 2:2"}],
          stderr_to_stdout: true
        )

      assert calibration =~ ~s("hé!")
      assert calibration =~ ~s(<<0, 33>>)
      assert length(Regex.scan(~r/badarg confirmed/, calibration)) == 6

      cases = [
        {"Marked", "decorate_text(<<104,195,169>>,true) == <<104,195,169,33>>"},
        {"Unmarked", "decorate_text(<<104,195,169>>,false) == <<104,195,169>>"},
        {"ZeroByte", "decorate_text(<<0>>,true) == <<0,33>>"},
        {"Empty", "owned_nonempty(<<>>) == false"},
        {"Nonempty", "owned_nonempty(<<104,195,169>>) == true"},
        {"None", "echo_text_option({nil,true}) == {nil,true}"},
        {"Some", "echo_text_option({<<104,195,169>>,false}) == {<<104,195,169>>,false}"}
      ]

      positive =
        for {name, expression} <- cases do
          expression = native_module <> "." <> expression
          [{_, beam}] = Code.compile_string(law(native_module, name, expression))
          beam
        end

      negative =
        for {name, call} <- [
              {"Malformed", "decorate_text(<<195,40>>,true)"},
              {"Truncated", "decorate_text(<<240,159>>,true)"},
              {"List", "decorate_text([97],true)"},
              {"Partial", "decorate_text(<<1::1>>,true)"},
              {"LaterArgument", "decorate_text(<<104,195,169>>,0)"},
              {"NestedMalformed", "echo_text_option({<<195,40>>,true})"}
            ] do
          expression =
            "try do #{native_module}." <>
              call <> "; false catch :error, :badarg -> true end"

          [{_, beam}] = Code.compile_string(law(native_module, name, expression))
          beam
        end

      beams = positive ++ negative
      export = Path.join(tmp, "text-input.export")
      reports = Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}, export: export)
      assert [] == for(r <- reports, r.status != :ok, do: r.diagnostics)
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
      files = Lynx.Translation.new(externals: [prepared.external]) |> Lynx.Translation.assemble()

      for path <- [
            Path.join(project, "TextInput/RustlerBridge.lean"),
            Path.join(project, "TextInput/Properties.lean")
          ],
          extra <- [
            "private axiom hidden_text : False",
            "private theorem unfinished_text : True := by sorry"
          ] do
        original = File.read!(path)
        File.write!(path, original <> "\n" <> extra <> "\n")
        Lynx.Rust.Project.build!(project, ["TextInput.Properties"])
        assert Enum.any?(Lynx.Commands.verify!(project, files), &(&1.status == :error))
        File.write!(path, original)
        Lynx.Rust.Project.build!(project, ["TextInput.Properties"])
      end

      path = Path.join(workspace, "analysis/src/lib.rs")
      original = File.read!(path)
      changed = String.replace(original, "append_owned(text, \"!\")", "append_owned(text, \"?\")")
      refute changed == original
      File.write!(path, changed)
      assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      File.write!(path, original)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end

  defp law(native_module, name, expression) do
    namespace = String.trim_trailing(native_module, ".Native")

    decoded =
      if name == "Nonempty" do
        """
        have decoded : Lynx.Rustler.decodeString (.bitstring ⟨#[104,195,169]⟩ 0) = .ok "hé" := by
          apply Lynx.Rustler.decodeString_valid
          · change 3 ≤ Aeneas.Std.Usize.max ∧ 3 ≤ Aeneas.Std.Isize.max.toNat
            constructor <;> cases System.Platform.numBits_eq <;> scalar_tac
          · decide +kernel
        """
      else
        ""
      end

    implementation =
      if name == "Nonempty", do: "simp [decoded, TextInput.Properties.facade_nonempty]", else: ""

    """
    defmodule #{namespace}.#{name} do
      @compile :debug_info
      use Lynx.Laws
      law classification,
        expects: (#{expression}),
        proof: ~LEAN\"\"\"
        #{decoded |> String.trim() |> String.replace("\n", "\n        ")}
        simp only [Lynx.apply,«classification:ensures/0»,
          Elixir.#{native_module}.«decorate_text/2»,
          Elixir.#{native_module}.«decorate_text:execution/2»,
          Elixir.#{native_module}.«owned_nonempty/1»,
          Elixir.#{native_module}.«owned_nonempty:execution/1»,
          Elixir.#{native_module}.«echo_text_option/1»,
          Elixir.#{native_module}.«echo_text_option:execution/1»]
        #{implementation}
        cbv
        all_goals
          rcases System.Platform.numBits_eq with platform | platform
          all_goals
            simp only [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits,
              Aeneas.Std.Isize.max, Aeneas.Std.Isize.numBits,
              Aeneas.Std.UScalarTy.numBits, Aeneas.Std.IScalarTy.numBits, platform]
            cbv
        \"\"\"
    end
    """
  end
end
