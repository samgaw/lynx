defmodule Lynx.Rustler.OrderedCollectionsTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for ordered collection NIF proofs")

  for version <- ["0.38.0", "0.39.0"] do
    @tag :tmp_dir
    test "composes ordered collection updates through Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      name = "LynxOrdered#{String.replace(version, ".", "")}Fixture.Native"
      native = String.to_atom("Elixir." <> name)
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
        |> String.replace("LynxRustFixture.Native", name)
        |> String.replace("LynxRustFixture.BinaryNative", name)

      rust =
        if @unpatched,
          do:
            "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
              Regex.replace(~r/(^#\[rustler::nif[^\n]*\]\n)/m, rust, "\\1#[verify::start_from]\n"),
          else: rust

      File.write!(source, rust)
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "Tables"))
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
        cargo: [features: ["ordered-collections"]],
        only: [
          ordered_replace: 3,
          ordered_claims: 1,
          ordered_stats: 4,
          ordered_take: 3,
          ordered_release: 2
        ],
        lean_project: project,
        module_prefix: "Tables.Extraction",
        build_dir: Path.join(tmp, "build")
      ]

      discovered = Lynx.Rustler.prepare!(base)
      bindings = Map.new(discovered.bindings.bindings, &{&1["name"], &1})

      assert %{
               "arguments" => ["u64", "u64", "u64"],
               "result" => %{"option" => "u64"},
               "flags" => 1
             } = bindings["ordered_replace"]

      assert %{
               "arguments" => ["u64"],
               "result" => %{"tuple" => ["bool", "bool", "u64"]},
               "flags" => 1
             } = bindings["ordered_claims"]

      assert %{
               "arguments" => ["u64", "u64", "u64", "u64"],
               "result" => %{"tuple" => [%{"option" => "u64"}, "u64"]},
               "flags" => 1
             } = bindings["ordered_stats"]

      properties =
        File.read!(Path.join(@proofs, "OrderedCollections.lean"))
        |> String.replace("experiment_analysis.core.borrow", "experiment_nif.core.borrow")
        |> String.replace("experiment_analysis.experiment_core", "experiment_nif.experiment_core")
        |> String.replace("experiment_analysis.", "experiment_nif.experiment_analysis.")

      File.write!(Path.join(project, "Tables/Properties.lean"), properties)

      adapter =
        File.read!(Path.join(@proofs, "OrderedCollectionsAdapter.lean"))
        |> String.replace("__REPLACE_NIF__", bindings["ordered_replace"]["lean_name"])
        |> String.replace("__CLAIMS_NIF__", bindings["ordered_claims"]["lean_name"])
        |> String.replace("__STATS_NIF__", bindings["ordered_stats"]["lean_name"])
        |> String.replace("__TAKE_NIF__", bindings["ordered_take"]["lean_name"])
        |> String.replace("__RELEASE_NIF__", bindings["ordered_release"]["lean_name"])

      File.write!(Path.join(project, "Tables/AdapterProperties.lean"), adapter)

      options =
        base ++
          [
            proof_modules: ["Tables.Properties", "Tables.AdapterProperties"],
            required_properties:
              Enum.map(
                ~w(internal_replace internal_claim replace duplicate stats borrow_identity internal_peek internal_take internal_contains internal_release take_preserves_other release_preserves_other take_once release_once),
                &("Tables.Properties." <> &1)
              ) ++
                Enum.map(
                  ~w(replace duplicate stats take_once release_once),
                  &("Tables.AdapterProperties." <> &1)
                )
          ]

      prepared = Lynx.Rustler.prepare!(options)
      assert Enum.all?(prepared.reports, &(&1.status == :ok))
      library = Path.join(tmp, "native")
      File.cp!(prepared.library, library <> ".so")

      stubs =
        for {function, arity, _} <- prepared.bindings.exports,
            do:
              "def #{function}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

      Code.compile_string("""
      defmodule #{name} do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
        #{Enum.join(stubs, "\n")}
      end
      """)

      assert %{
               "arguments" => ["u64", "u64", "u64"],
               "result" => %{
                 "tuple" => [
                   %{"option" => "u64"},
                   %{"option" => "u64"},
                   %{"option" => "u64"},
                   "u64"
                 ]
               },
               "flags" => 1
             } = bindings["ordered_take"]

      assert %{
               "arguments" => ["u64", "u64"],
               "result" => %{"tuple" => ["bool", "bool", "bool", "bool", "u64"]},
               "flags" => 1
             } = bindings["ordered_release"]

      assert apply(native, :ordered_take, [7, 11, 7]) == {11, 11, nil, 0}
      assert apply(native, :ordered_take, [7, 11, 8]) == {nil, nil, nil, 1}
      assert apply(native, :ordered_release, [7, 7]) == {true, true, false, false, 0}
      assert apply(native, :ordered_release, [7, 8]) == {false, false, false, false, 1}
      assert_raise ArgumentError, fn -> apply(native, :ordered_take, [7, :bad, 7]) end

      assert_raise ArgumentError, fn ->
        apply(native, :ordered_release, [7, 18_446_744_073_709_551_616])
      end

      assert apply(native, :ordered_replace, [7, 11, 42]) == 11
      assert apply(native, :ordered_claims, [7]) == {true, false, 1}
      assert apply(native, :ordered_stats, [7, 11, 7, 42]) == {11, 1}
      assert apply(native, :ordered_stats, [7, 11, 8, 42]) == {nil, 2}
      max = 18_446_744_073_709_551_615
      assert apply(native, :ordered_replace, [max, max, 0]) == max

      for args <- [[-1], [max + 1], [:not_integer]],
          do: assert_raise(ArgumentError, fn -> apply(native, :ordered_claims, args) end)

      cases = [
        {"Take", "#{name}.ordered_take(7,11,7) == {11,11,nil,0}"},
        {"MissingTake", "#{name}.ordered_take(7,11,8) == {nil,nil,nil,1}"},
        {"MaximumTake",
         "#{name}.ordered_take(18446744073709551615,18446744073709551615,18446744073709551615) == {18446744073709551615,18446744073709551615,nil,0}"},
        {"Release", "#{name}.ordered_release(7,7) == {true,true,false,false,0}"},
        {"MissingRelease", "#{name}.ordered_release(7,8) == {false,false,false,false,1}"},
        {"WrongTakeType",
         "try do #{name}.ordered_take(7,:bad,7); false catch :error, :badarg -> true end"},
        {"ReleaseOverflow",
         "try do #{name}.ordered_release(7,18446744073709551616); false catch :error, :badarg -> true end"},
        {"Replace", "#{name}.ordered_replace(7,11,42) == 11"},
        {"Claims", "#{name}.ordered_claims(7) == {true,false,1}"},
        {"SameKey", "#{name}.ordered_stats(7,11,7,42) == {11,1}"},
        {"DistinctKeys", "#{name}.ordered_stats(7,11,8,42) == {nil,2}"},
        {"Maximum",
         "#{name}.ordered_replace(18446744073709551615,18446744073709551615,0) == 18446744073709551615"},
        {"Negative",
         "try do #{name}.ordered_claims(-1); false catch :error, :badarg -> true end"},
        {"Overflow",
         "try do #{name}.ordered_claims(18446744073709551616); false catch :error, :badarg -> true end"},
        {"WrongType",
         "try do #{name}.ordered_claims(:not_integer); false catch :error, :badarg -> true end"}
      ]

      beams =
        for {suffix, expression} <- cases do
          [{_, beam}] = Code.compile_string(law(name, suffix, expression))
          beam
        end

      export = Path.join(tmp, "ordered.export")
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

  defp law(native, suffix, expression) do
    """
    defmodule #{String.trim_trailing(native, ".Native")}.#{suffix} do
      @compile :debug_info
      use Lynx.Laws
      law ordered,
        expects: (#{expression}),
        proof: ~LEAN\"\"\"
        simp only [Lynx.apply, «ordered:ensures/0»,
          Elixir.#{native}.«ordered_replace/3», Elixir.#{native}.«ordered_replace:execution/3»,
          Elixir.#{native}.«ordered_claims/1», Elixir.#{native}.«ordered_claims:execution/1»,
          Elixir.#{native}.«ordered_stats/4», Elixir.#{native}.«ordered_stats:execution/4»,
          Elixir.#{native}.«ordered_take/3», Elixir.#{native}.«ordered_take:execution/3»,
          Elixir.#{native}.«ordered_release/2», Elixir.#{native}.«ordered_release:execution/2»]
        cbv
        \"\"\"
    end
    """
  end
end
