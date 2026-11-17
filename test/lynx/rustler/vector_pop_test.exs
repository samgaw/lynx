defmodule Lynx.Rustler.VectorPopTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR") || System.get_env("LYNX_PURE_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for Vec pop NIF proofs")

  for version <- ~w(0.39.0 0.38.0) do
    @tag :tmp_dir
    test "proves pop and retained records through Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      prefix = "VectorPop" <> String.replace(version, ".", "")
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for name <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
          do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

      source = Path.join(workspace, "nif/src/lib.rs")

      File.write!(
        source,
        "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
          (File.read!(source)
           |> String.replace("LynxRustFixture.Native", prefix <> ".Native")
           |> String.replace("fn take_record(", "#[verify::start_from]\nfn take_record("))
      )

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, prefix))
      File.mkdir_p!(Path.join(project, ".lake"))

      File.ln_s!(
        Path.join(@fixture, "proofs/.lake/packages"),
        Path.join(project, ".lake/packages")
      )

      base = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        root_attribute: "verify::start_from",
        cargo: [features: ["pop-vec"]],
        only: [pop_record: 1],
        lean_project: project,
        module_prefix: prefix <> ".Extraction",
        build_dir: Path.join(tmp, "build")
      ]

      discovered = Lynx.Rustler.prepare!(base)

      assert [
               %{
                 "name" => "pop_record",
                 "arity" => 1,
                 "flags" => 0,
                 "arguments" => [%{"vec" => "i64"}],
                 "result" => %{"tuple" => [%{"option" => "i64"}, %{"vec" => "i64"}]},
                 "lean_name" => facade
               }
             ] = discovered.bindings.bindings

      for {template, file} <- [
            {"VectorPop.lean", "Properties.lean"},
            {"VectorPopBoundary.lean", "Boundary.lean"}
          ] do
        proof =
          File.read!(Path.join(@proofs, template))
          |> String.replace("__PREFIX__", prefix)
          |> String.replace("__CORE__", "experiment_nif.experiment_core.collections")
          |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")
          |> String.replace("__FACADE__", facade)

        File.write!(Path.join(project, prefix <> "/" <> file), proof)
      end

      options =
        base ++
          [
            proof_modules: [prefix <> ".Properties", prefix <> ".Boundary"],
            required_properties:
              Enum.map(
                ~w(internal_spec composition empty_unchanged last_and_prefix length_decreases),
                &(prefix <> ".Properties." <> &1)
              ) ++ [prefix <> ".Boundary.facade_spec"]
          ]

      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.all?(prepared.reports, &(&1.status == :ok))

      assert Enum.any?(
               prepared.verification.external_models,
               &String.contains?(&1, "Logical standard Vec::pop model")
             )

      assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
      library = Path.join(tmp, "native")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {name, arity, _} <- prepared.bindings.exports,
            do:
              "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      Code.compile_string("""
      defmodule #{prefix}.Native do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}",0)
        #{Enum.join(stubs, "\n")}
      end
      """)

      [{module, beam}] =
        File.read!(Path.join(@proofs, "vector_pop_laws.ex"))
        |> String.replace("__MODULE__", prefix)
        |> Code.compile_string()

      for law <-
            ~w(last_record empty singleton signed_bounds invalid_record out_of_range bad_head_before_tail improper_tail)a,
          do: assert(apply(module, law, []))

      export = Path.join(tmp, "pop.export")
      law_options = [native: {Lynx.Rustler, options}]
      reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
      assert [] == for(r <- reports, r.status != :ok, do: {r.module, r.diagnostics})
      assert length(Enum.flat_map(reports, & &1.theorems)) == 8
      assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
      property = Path.join(project, prefix <> "/Boundary.lean")
      proof = File.read!(property)
      wrong = String.replace(proof, "input.val.getLast?", "none")
      refute wrong == proof
      File.write!(property, wrong)
      assert_raise RuntimeError, fn -> Lynx.Rustler.prepare!(options) end
      File.write!(property, proof)
    end
  end
end
