defmodule Lynx.Rustler.CustomTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for custom Rustler NIF proofs")

  for version <- ["0.38.0", "0.39.0"] do
    @tag tmp_dir: "process-#{System.pid()}"
    test "automatically prepares the custom NIF under Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = if version == "0.38.0", do: "38", else: "39"
      module = "LynxRustFixture.Custom#{suffix}Native"
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for file <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
          do: File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))
      rust_source = Path.join(workspace, "nif/src/lib.rs")

      File.write!(
        rust_source,
        String.replace(File.read!(rust_source), "LynxRustFixture.Native", module)
      )

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output
      project = Path.join(tmp, "proofs")
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      options = [
        tools: @tools,
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "CustomNif.Extraction",
        cargo: [features: ["custom-encoder"]],
        only: [custom_validate: 1]
      ]

      prepared = Lynx.Rustler.prepare!(workspace, "experiment-nif", options)
      assert prepared.bindings.module == "Elixir." <> module

      assert [
               %{
                 "result" => %{
                   "result" => [
                     %{"tuple" => []},
                     %{
                       "native" => ["experiment_nif", "custom_encoding", "Error"],
                       "encoder" => encoder
                     }
                   ]
                 }
               }
             ] =
               prepared.bindings.bindings

      assert String.ends_with?(encoder, ".encode")
      assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

      [entry] = prepared.bindings.bindings

      wrong_type =
        put_in(entry, ["result", "result", Access.at(1), "native"], [
          "experiment_nif",
          "custom_encoding",
          "Unrelated"
        ])

      assert_raise ArgumentError, ~r/custom NIF result requires/, fn ->
        Lynx.Rustler.Bindings.link!(
          %{prepared.bindings | bindings: [wrong_type]},
          prepared.extraction.audit,
          prepared.extraction.translation
        )
      end

      codec_id = get_in(entry, ["result", "result", Access.at(1), "encoder_definition_id"])

      incomplete = %{
        prepared.extraction.audit
        | functions: Enum.reject(prepared.extraction.audit.functions, &(&1["def_id"] == codec_id))
      }

      assert_raise ArgumentError,
                   ~r/missing, opaque or mismatched first-party Rustler Encoder/,
                   fn ->
                     Lynx.Rustler.Bindings.link!(
                       prepared.bindings,
                       incomplete,
                       prepared.extraction.translation
                     )
                   end

      binding = hd(prepared.bindings.bindings)

      implementations =
        Enum.map(Map.values(prepared.extraction.implementations), & &1["lean_name"])

      dictionaries = Enum.map(prepared.extraction.translation["trait_impls"], & &1["lean_name"])

      unfold =
        Enum.join(
          implementations ++
            dictionaries ++
            [
              "CustomNif.Extraction.RustlerAtomCache.cache_0",
              "Lynx.Rustler.Encoding.pair",
              "Lynx.Rustler.Encoding.shared",
              "Lynx.Rustler.Encoding.atom",
              "Lynx.Rustler.Encoding.string",
              "Lynx.RustFormatting.alloc.string.ToString.to_string",
              "Lynx.RustFormatting.core.fmt.DisplayStr.fmt",
              "Lynx.RustFormatting.core.fmt.Formatter.write_str",
              "Lynx.RustFormatting.Formatting.writeBytes",
              "Lynx.RustFormatting.Formatting.append"
            ],
          ", "
        )

      File.write!(Path.join(project, "CustomNif/Properties.lean"), """
      module
      public import CustomNif.Extraction.Funs
      public section
      open Aeneas Aeneas.Std
      set_option linter.unusedSimpArgs false
      namespace CustomNif.Properties
      theorem invert (value : Bool) : experiment_nif.experiment_core.invert value = RustM.ok (!value) := by
        cases value <;> rfl
      theorem restore (value : Bool) : experiment_nif.experiment_analysis.restore value = RustM.ok value := by
        simp [experiment_nif.experiment_analysis.restore, invert]
      theorem success : #{binding["lean_name"]} (⟨BitVec.ofNat 8 2⟩ : U8) = RustM.ok (.Ok ()) := by
        change #{binding["lean_name"]} 2#u8 = RustM.ok (.Ok ())
        simp [#{unfold}]
      theorem missing : #{binding["lean_name"]} (⟨BitVec.ofNat 8 0⟩ : U8) = RustM.ok (.Err .Missing) := by
        change #{binding["lean_name"]} 0#u8 = RustM.ok (.Err .Missing)
        simp [#{unfold}]
      theorem invalid : #{binding["lean_name"]} (⟨BitVec.ofNat 8 1⟩ : U8) = RustM.ok (.Err (.Invalid "custom error")) := by
        change #{binding["lean_name"]} 1#u8 = RustM.ok (.Err (.Invalid "custom error"))
        have decoded : String.fromUTF8? ⟨(Lynx.RustFormatting.Formatting.bytes (toStr "custom error").val).toList.toArray⟩ =
            some "custom error" := by decide +kernel
        have bounded : "custom error".utf8ByteSize ≤ 4294967295 := by decide +kernel
        simp [#{unfold}, decoded, bounded]
      theorem encode_missing : #{encoder} .Missing () = RustM.ok (.atom "missing") := by
        simp [#{unfold}]
      theorem encode_invalid : #{encoder} (.Invalid "custom error") () =
          RustM.ok (.tuple #[.atom "invalid", .bitstring "custom error".toUTF8 0]) := by
        have bounded : "custom error".utf8ByteSize ≤ 4294967295 := by decide +kernel
        simp [#{unfold}, bounded]
      end CustomNif.Properties
      """)

      Lynx.Rust.Project.build!(project, ["CustomNif.Properties"])

      native_path = Path.join(tmp, "custom_native")
      File.cp!(prepared.library, native_path <> ".so")

      stubs =
        Enum.map_join(prepared.bindings.exports, "\n", fn {name, arity, _} ->
          "def #{name}(#{Enum.join(List.duplicate("_", arity), ", ")}), do: :erlang.nif_error(:not_loaded)"
        end)

      source = Path.join(tmp, "native.ex")

      File.write!(source, """
      defmodule #{module} do
        @compile :debug_info
        @on_load :load_native
        def load_native, do: :erlang.load_nif(~c"#{native_path}", 0)
        #{stubs}
      end
      """)

      assert {:ok, [_], _} =
               Kernel.ParallelCompiler.compile_to_path([source], tmp, return_diagnostics: true)

      native_module = String.to_atom("Elixir." <> module)
      assert apply(native_module, :custom_validate, [2]) == {:ok, {}}
      assert apply(native_module, :custom_validate, [0]) == {:error, :missing}
      assert apply(native_module, :custom_validate, [1]) == {:error, {:invalid, "custom error"}}
      assert apply(native_module, :custom_validate, [256]) == {:error, :missing}

      for value <- [-1, 4_294_967_296],
          do:
            assert_raise(ArgumentError, fn -> apply(native_module, :custom_validate, [value]) end)

      laws =
        for {name, input, expected} <- [
              {"success", 2, "{:ok, {}}"},
              {"missing", 0, "{:error, :missing}"},
              {"invalid", 1, "{:error, {:invalid, \"custom error\"}}"},
              {"narrowing", 256, "{:error, :missing}"}
            ] do
          finish = if name == "invalid", do: "exact Lynx.Term.compare_self _", else: ""

          ~s'''
          law #{name}, expects: #{module}.custom_validate(#{input}) == #{expected}, proof: ~LEAN"""
          simp [«#{name}:ensures/0», Elixir.#{module}.«custom_validate/1»,
            Elixir.#{module}.«custom_validate:execution/1», CustomNif.Properties.success,
            CustomNif.Properties.missing, CustomNif.Properties.invalid,
            CustomNif.Properties.encode_missing, CustomNif.Properties.encode_invalid,
              Lynx.Rustler.decodeUnsigned, Lynx.Rustler.encodeResultM, Erlang.erlang.«==/2»]
          #{finish}
          """
          '''
        end

      badarg =
        for {name, input} <- [{"negative", -1}, {"too_large", 4_294_967_296}] do
          ~s'''
          law #{name}, expects: (try do #{module}.custom_validate(#{input}); false
            catch :error, :badarg -> true end), proof: ~LEAN"""
          simp [«#{name}:ensures/0», Elixir.#{module}.«custom_validate/1»,
            Lynx.Rustler.decodeUnsigned, Lynx.Exception.classTerm, Lynx.Exception.reason]
          """
          '''
        end

      law_source = Path.join(tmp, "laws.ex")

      File.write!(
        law_source,
        "defmodule LynxRustFixture.Custom#{suffix}Laws do\n" <>
          "@compile :debug_info\nuse Lynx.Laws\n" <> Enum.join(laws ++ badarg, "\n") <> "\nend\n"
      )

      [{_, beam}] = Code.compile_file(law_source)

      reports =
        Lynx.Laws.verify([beam],
          native:
            {Lynx.Rustler,
             [
               workspace: workspace,
               package: "experiment-nif",
               proof_modules: ["CustomNif.Properties"],
               required_properties: [
                 "CustomNif.Properties.restore",
                 "CustomNif.Properties.success",
                 "CustomNif.Properties.invalid"
               ]
             ] ++ options}
        )

      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

      assert Enum.any?(reports, fn report ->
               Enum.any?(Map.get(report, :guarantees, []), &(&1.kind == :elixir_law))
             end)

      guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

      assert Enum.any?(
               guarantees,
               &(&1.kind == :rust_implementation and &1.rust_name == "experiment_core::invert")
             )

      assert Enum.any?(
               guarantees,
               &(&1.kind == :cross_crate_contract and
                   &1.theorem == "CustomNif.Properties.restore" and
                   "CustomNif.Properties.invert" in &1.contracts_used)
             )

      if version == "0.39.0" do
        original = File.read!(rust_source)

        changed =
          String.replace(
            original,
            "Self::Missing => missing().encode(env)",
            "Self::Missing => invalid().encode(env)"
          )

        assert changed != original
        File.write!(rust_source, changed)

        error =
          assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
            Lynx.Rustler.prepare!(
              workspace,
              "experiment-nif",
              [
                proof_modules: ["CustomNif.Properties"],
                required_properties: ["CustomNif.Properties.encode_missing"]
              ] ++ options
            )
          end

        assert Exception.message(error) =~ "CustomNif/Properties.lean"
        assert Exception.message(error) =~ "unsolved goals"
      end
    end
  end
end
