defmodule Lynx.Rustler.CompositeTest do
  use ExUnit.Case

  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "verifies tuple and result NIFs composed through shared first-party types", %{tmp_dir: tmp} do
    prepared =
      Lynx.Rustler.prepare!(@fixture, "experiment-nif",
        lean_project: Path.join(@fixture, "proofs"),
        module_prefix: "RustWorkspace.CompositeFacade",
        cargo: [features: ["composite"]],
        proof_modules: ["RustWorkspace.Composite"],
        required_properties: [
          "RustWorkspace.Composite.decide_spec",
          "RustWorkspace.Composite.classify_spec"
        ],
        only: [transform_pair: 1, classify: 1, reverse_result: 1, echo_nested: 1, echo_seven: 1]
      )

    assert Enum.count(prepared.verification.guarantees, &(&1.kind == :nif_adapter)) == 5

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract &&
               evidence.theorem == "RustWorkspace.Composite.classify_spec" &&
               "RustWorkspace.Composite.decide_spec" in evidence.contracts_used
           end)

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :rust_implementation &&
               evidence.theorem == "RustWorkspace.Composite.decide_spec" &&
               String.ends_with?(evidence.file, "core/src/lib.rs")
           end)

    assert length(prepared.verification.unverified_nif_exports) == 10

    File.mkdir_p!(Path.join(@fixture, "priv"))
    File.cp!(prepared.library, Path.join(@fixture, "priv/libexperiment_composite.so"))

    assert {:ok, [LynxRustFixture.CompositeNative], _} =
             Kernel.ParallelCompiler.compile_to_path(
               [Path.join(@fixture, "elixir/composite_native.ex")],
               tmp,
               return_diagnostics: true
             )

    module = LynxRustFixture.CompositeNative
    assert apply(module, :transform_pair, [{true, 42}]) == {false, 42}

    assert apply(module, :classify, [{true, -9_223_372_036_854_775_808}]) ==
             {:ok, -9_223_372_036_854_775_808}

    assert apply(module, :classify, [{false, 42}]) == {:error, 7}
    assert apply(module, :reverse_result, [{:ok, 5}]) == {:error, 5}
    assert apply(module, :reverse_result, [{:error, 256}]) == {:ok, 0}
    assert apply(module, :echo_nested, [{{true}, {256, -1, {}}}]) == {{true}, {0, -1, {}}}
    assert apply(module, :echo_seven, [{1, 2, 3, 4, 5, 6, 256}]) == {1, 2, 3, 4, 5, 6, 0}

    for {function, inputs} <- [
          transform_pair: [
            true,
            [],
            {},
            {true},
            {true, 1, 2},
            {0, 1},
            {true, 9_223_372_036_854_775_808}
          ],
          reverse_result: [
            true,
            {:ok},
            {:ok, 1, 2},
            {:other, 1},
            {true, 1},
            {:ok, true},
            {:error, -1},
            {:error, 4_294_967_296}
          ],
          echo_nested: [{{true, false}, {0, 1, {}}}, {{true}, {0, 1, {1}}}]
        ],
        input <- inputs do
      assert_raise ArgumentError, fn -> apply(module, function, [input]) end
    end

    compiled = Lynx.Rustler.Metadata.inspect!(prepared.library)
    discovered = Lynx.Rustler.Metadata.bindings!(prepared.expanded, compiled, classify: 1)
    [binding] = discovered.bindings

    assert %{
             "arguments" => [%{"tuple" => ["bool", "i64"]}],
             "result" => %{"result" => ["i64", "u8"]}
           } = binding

    changed = %{discovered | bindings: [%{binding | "result" => %{"result" => ["i64", "bool"]}}]}

    assert_raise ArgumentError, ~r/Rustler and LLBC signatures differ/, fn ->
      Lynx.Rustler.Bindings.link!(
        changed,
        prepared.extraction.audit,
        prepared.extraction.translation
      )
    end

    [{_, beam}] = Code.compile_file(Path.join(@fixture, "elixir/composite_laws.ex"))

    reports =
      Lynx.Laws.verify([beam], externals: [prepared.external], lean_project: prepared.project)

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(reports, pretty: true, limit: :infinity)

    warm =
      Lynx.Laws.verify([beam], externals: [prepared.external], lean_project: prepared.project)

    assert Enum.all?(warm, &(&1.status == :ok && &1.cached))

    export = Path.join(tmp, "composite.export")

    checked =
      Lynx.Laws.verify([beam],
        externals: [prepared.external],
        lean_project: prepared.project,
        export: export
      )

    assert Enum.all?(checked, &(&1.status == :ok)), inspect(checked, limit: :infinity)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

    {status, output} =
      Lynx.Commands.lake(prepared.project, ["check", "--from-export", export] ++ sandbox)

    assert status == 0, output
  end
end
