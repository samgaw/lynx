defmodule Lynx.Rust.VectorPopTest do
  use ExUnit.Case
  alias Lynx.Rust.{CallModels, CollectionModels, LLBC}
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/VectorPop.lean", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR") || System.get_env("LYNX_PURE_AENEAS_DIR") ||
           System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for Vec pop proofs")

  @tag :tmp_dir
  test "proves generic removal and composes exact retained prefixes across crates", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for name <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "PopStandalone"))
    File.mkdir_p!(Path.join(project, ".lake"))
    File.ln_s!(Path.join(@fixture, "proofs/.lake/packages"), Path.join(project, ".lake/packages"))
    property = Path.join(project, "PopStandalone/Properties.lean")

    proof =
      File.read!(@proof)
      |> String.replace("__PREFIX__", "PopStandalone")
      |> String.replace("__CORE__", "experiment_analysis.experiment_core.collections")
      |> String.replace("__ANALYSIS__", "experiment_analysis")

    File.write!(property, proof)

    options = [
      tools: @tools,
      roots: ["experiment_analysis::pop_record"],
      mir: :elaborated,
      lean_project: project,
      module_prefix: "PopStandalone.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["PopStandalone.Properties"],
      required_properties:
        Enum.map(
          ~w(internal_spec composition empty_unchanged last_and_prefix length_decreases),
          &("PopStandalone.Properties." <> &1)
        )
    ]

    prepared = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert Enum.any?(
             prepared.verification.external_models,
             &String.contains?(&1, "Logical standard Vec::pop model")
           )

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract and
               evidence.theorem == "PopStandalone.Properties.composition" and
               "PopStandalone.Properties.internal_spec" in evidence.contracts_used
           end)

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok and &1.cached)
           )

    audit = prepared.extraction.audit

    {_, model} =
      Enum.find(audit.external_calls, fn {_, model} -> model[:vec_owned_method] == "pop" end)

    assert model.implementation_verified == false
    function = CallModels.expand(model.function, audit.references)

    for bad <- [
          put_in(function, ["signature", "is_unsafe"], true),
          update_in(function, ["signature", "inputs", Access.at(0), "Ref"], fn [
                                                                                 region,
                                                                                 type,
                                                                                 "Mut"
                                                                               ] ->
            [region, type, "Shared"]
          end),
          put_in(function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(function, ["generics", "outlives"], []),
          put_in(function, ["item_meta", "name", Access.at(0)], %{"Ident" => ["user", 0]})
        ],
        do: assert(CollectionModels.resolve(bad, audit.translated, audit.references) == nil)

    document = File.read!(prepared.extraction.llbc) |> JSON.decode!()
    declarations = document["translated"]["type_decls"]

    allocator =
      Enum.find_index(
        declarations,
        &(&1 &&
            &1["item_meta"]["name"] ==
              Enum.map(~w(alloc alloc Global), fn name -> %{"Ident" => [name, 0]} end))
      )

    refute is_nil(allocator)

    wrong_allocator =
      put_in(document, ["translated", "type_decls", Access.at(allocator), "item_meta", "name"], [
        %{"Ident" => ["CustomAllocator", 0]}
      ])

    assert_raise CompileError, ~r/unsupported Vec::pop: only the standard Global allocator/, fn ->
      LLBC.audit!(wrong_allocator, audit.first_party)
    end

    for extra <- [
          "private axiom popTrust : False",
          "private theorem unfinishedPop : True := by sorry"
        ] do
      File.write!(property, proof <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/audit/, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end
    end

    File.write!(property, String.replace(proof, "input.val.getLast?", "input.val.head?"))

    assert_raise RuntimeError, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(property, proof)
    core = Path.join(workspace, "core/src/collections.rs")
    original = File.read!(core)

    changed =
      String.replace(original, "    input.pop()", "    None")

    refute changed == original
    File.write!(core, changed)

    assert_raise RuntimeError, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(core, original)
  end
end
