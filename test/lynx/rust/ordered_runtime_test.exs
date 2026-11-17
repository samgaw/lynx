defmodule Lynx.Rust.OrderedRuntimeTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @properties Path.expand("../../fixtures/rust_protocol/OrderedRuntime.lean", __DIR__)
  @tools System.get_env("LYNX_NATIVE_COLLECTIONS_DIR")
  @moduletag timeout: 900_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_NATIVE_COLLECTIONS_DIR for shared ordered collection proofs")

  @tag :tmp_dir
  test "composes locked ordered updates with lossless shared heap contents", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for name <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@workspace, name), Path.join(workspace, name))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Registry"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.join(@workspace, "proofs/.lake/packages"),
      Path.join(project, ".lake/packages")
    )

    properties = Path.join(project, "Registry/Properties.lean")

    proof =
      File.read!(@properties)
      |> String.replace("__PREFIX__", "Registry")
      |> String.replace("__CORE__", "experiment_analysis.experiment_core.ordered")
      |> String.replace("__ANALYSIS__", "experiment_analysis")

    File.write!(properties, proof)

    snapshot =
      File.read!(Path.join(Path.dirname(@properties), "OrderedSnapshot.lean"))
      |> String.replace("__PREFIX__", "Registry")
      |> String.replace("__CORE__", "experiment_analysis.experiment_core.ordered")
      |> String.replace("__ANALYSIS__", "experiment_analysis")

    File.write!(Path.join(project, "Registry/Snapshots.lean"), snapshot)

    options = [
      tools: @tools,
      execution: :runtime,
      nonpanicking: [
        {"experiment_core::ordered::first_key", "Registry.Properties.first_key_no_panic"}
      ],
      sysroot: :full_mir,
      lean_project: project,
      module_prefix: "Registry.Extraction",
      build_dir: Path.join(tmp, "build"),
      roots:
        ~w(experiment_analysis::registry_replace experiment_analysis::registry_take experiment_analysis::registry_claim experiment_analysis::registry_first_key experiment_analysis::registry_pairs),
      proof_modules: ["Registry.Properties", "Registry.Snapshots"],
      required_properties:
        Enum.map(
          ~w(replace_eq locked_contract replace_run replace_preserves_other take_eq take_contract take_run claim_eq claim_contract claim_run first_key_eq first_key_no_panic first_key_contract first_key_run),
          &("Registry.Properties." <> &1)
        ) ++
          Enum.map(
            ~w(pairs_snapshot pairs_outcome pairs_total pairs_contract pairs_run),
            &("Registry.Snapshots." <> &1)
          )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert Enum.all?(result.reports, &(&1.status == :ok))
    assert [%{bytes: 16}] = result.extraction.tuple_layouts.queries

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok and &1.cached)
           )

    assert Enum.all?(
             result.verification.unverified_external_calls,
             &(not &1.implementation_verified)
           )

    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    export = Path.join(tmp, "registry.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    core = Path.join(workspace, "core/src/ordered.rs")
    original = File.read!(core)

    for {before, after_text} <- [
          {"replace_value(&mut guard, key, value)", "replace_value(&mut guard, 0, value)"},
          {"take(&mut guard, key)", "take(&mut guard, 0)"},
          {"claim(&mut guard, key)", "claim(&mut guard, 0)"},
          {".map(|(key, _)| *key)", ".map(|(_key, _)| 0)"},
          {"output.push((*key, *value))", "output.push((*value, *key))"}
        ] do
      changed = String.replace(original, before, after_text)
      refute changed == original
      File.write!(core, changed)

      assert_raise RuntimeError, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

      File.write!(core, original)
    end

    wrong = String.replace(proof, "(.ok table[key.val]?,", "(.ok none,")
    refute wrong == proof
    File.write!(properties, wrong)

    assert_raise RuntimeError, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(properties, proof)

    heap = Path.join(project, "Registry/Extraction/OrderedCollectionHeap.lean")
    contents = File.read!(heap)

    for extra <- [
          "private axiom unapproved_heap : False",
          "private theorem unfinished_heap : True := by sorry"
        ] do
      File.write!(heap, contents <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(heap, contents)
    end

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok)
           )
  end
end
