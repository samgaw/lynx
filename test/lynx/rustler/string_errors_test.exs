defmodule Lynx.Rustler.StringErrorsTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for boxed String proofs")

  for version <- ["0.38.0", "0.39.0"] do
    @tag :tmp_dir
    test "proves boxed String payloads with Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      suffix = String.replace(version, ".", "")
      native_module = "LynxString#{suffix}.Native"
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for name <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
          do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output
      path = Path.join(workspace, "nif/src/lib.rs")
      source = String.replace(File.read!(path), "LynxRustFixture.Native", native_module)

      source =
        "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
          Enum.reduce(~w(string_error string_returned), source, fn name, s ->
            String.replace(s, "fn #{name}(", "#[verify::start_from]\nfn #{name}(")
          end)

      File.write!(path, source)
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "StringErrors"))
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        root_attribute: "verify::start_from",
        cargo: [features: ["string-errors"]],
        only: [string_error: 1, string_term: 1],
        mir: :elaborated,
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "StringErrors.Extraction"
      ]

      prepared = Lynx.Rustler.prepare!(options)
      bindings = Map.new(prepared.bindings.bindings, &{&1["name"], &1})

      properties =
        File.read!(Path.join(@fixture, "proofs/RustWorkspace/StringErrors.lean"))
        |> String.replace("__RAISED__", bindings["string_error"]["lean_name"])
        |> String.replace("__RETURNED__", bindings["string_term"]["lean_name"])

      property = Path.join(project, "StringErrors/Properties.lean")
      File.write!(property, properties)

      options =
        options ++
          [
            proof_modules: ["StringErrors.Properties"],
            required_properties:
              Enum.map(
                ~w(core_preserve_spec analysis_preserve_spec text_spec raised_spec returned_spec raised_seven returned_seven),
                &("StringErrors.Properties." <> &1)
              )
          ]

      verified = Lynx.Rustler.prepare!(options)
      assert Enum.all?(verified.reports, &(&1.status == :ok))
      assert Enum.any?(verified.verification.guarantees, &(&1.kind == :cross_crate_contract))

      assert Enum.any?(
               verified.verification.unverified_external_calls,
               &(String.contains?(&1.rust_name, "Encoder<alloc::string::String>") &&
                   !&1.implementation_verified)
             )

      assert Enum.any?(
               verified.verification.structural_drops,
               &(&1.type == "alloc::string::String" && &1.status == :modelled &&
                   !&1.implementation_verified)
             )

      library = Path.join(tmp, "string_native")
      File.cp!(verified.library, library <> ".so")

      stubs =
        for {name, arity, _} <- verified.bindings.exports,
            do:
              "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      [{native, _}] =
        Code.compile_string("""
        defmodule #{native_module} do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(~c"#{library}",0)
          #{Enum.join(stubs, "\n")}
        end
        """)

      for value <- [0, 7, 18_446_744_073_709_551_615] do
        assert catch_error(apply(native, :string_error, [value])) == "λvalue=#{value}"
        assert apply(native, :string_term, [value]) == {:error, "λvalue=#{value}"}
      end

      for target <- [:string_error, :string_term],
          value <- [-1, 18_446_744_073_709_551_616, :invalid],
          do: assert_raise(ArgumentError, fn -> apply(native, target, [value]) end)

      [{_, beam}] = Code.compile_string(laws(native_module, suffix))
      export = Path.join(tmp, "string.export")
      reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

      assert Enum.all?(
               Lynx.Laws.verify([beam], lean_project: project, externals: [verified.external]),
               &(&1.status == :ok && &1.cached)
             )

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      for extra <- [
            "private axiom stringTrust : False",
            "private theorem unfinishedString : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      File.write!(property, properties)
      changed = String.replace(source, "λvalue={value}", "λvalue=0{value}")
      refute changed == source
      File.write!(path, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(path, source)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end

  defp laws(native, suffix) do
    """
    defmodule LynxString#{suffix}.Laws do
      @compile :debug_info
      use Lynx.Laws
      law raised(), expects: (try do #{native}.string_error(7) catch :error, reason -> reason == "λvalue=7" end),
        proof: ~LEAN\"\"\"
        have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 7) = .ok (7#u64) := by
          have encoded : Lynx.Rustler.encodeUnsigned (7#u64) = .integer 7 := by rfl
          rw [← encoded]
          exact Lynx.Rustler.decodeUnsigned_encodeUnsigned _
        have bytes : "λvalue=7".toByteArray = ({ data := #[206,187,118,97,108,117,101,61,55] } : ByteArray) := by
          apply ByteArray.ext
          simp
          decide +kernel
        simp [bytes, «raised:ensures/0», Elixir.#{native}.«string_error/1»,
          Elixir.#{native}.«string_error:execution/1», decoded,
          StringErrors.Properties.raised_seven, Erlang.erlang.«==/2»,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        \"\"\"
      law returned(), expects: #{native}.string_term(7) == {:error,"λvalue=7"},
        proof: ~LEAN\"\"\"
        have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 7) = .ok (7#u64) := by
          have encoded : Lynx.Rustler.encodeUnsigned (7#u64) = .integer 7 := by rfl
          rw [← encoded]
          exact Lynx.Rustler.decodeUnsigned_encodeUnsigned _
        have bytes : "λvalue=7".toByteArray = ({ data := #[206,187,118,97,108,117,101,61,55] } : ByteArray) := by
          apply ByteArray.ext
          simp
          decide +kernel
        simp [bytes, «returned:ensures/0», Elixir.#{native}.«string_term/1»,
          Elixir.#{native}.«string_term:execution/1», decoded,
          StringErrors.Properties.returned_seven, Erlang.erlang.«==/2»]
        \"\"\"
    end
    """
  end
end
