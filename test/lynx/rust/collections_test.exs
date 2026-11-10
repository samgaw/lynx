defmodule Lynx.Rust.CollectionsTest do
  use ExUnit.Case
  alias Lynx.Rust.{CallModels, LLBC}

  @tools System.get_env("LYNX_AENEAS_DIR")
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_collections/Properties.lean", __DIR__)
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for Rust collection proofs")

  @tag tmp_dir: "process-#{System.pid()}"
  test "proves actual Vec view mutation, cross-crate contracts and bounds panics", %{tmp_dir: tmp} do
    workspace = workspace(tmp)
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Collections"))
    File.cp!(@proof, Path.join(project, "Collections/Properties.lean"))
    packages = Path.join(@workspace, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots:
        Enum.map(
          ~w(replace_first slice_length replace_at batch_length result_is_ok),
          &("experiment_analysis::" <> &1)
        ) ++ ["experiment_core::collections::batch_length"],
      mir: :elaborated,
      lean_project: project,
      module_prefix: "Collections.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Collections.Properties"],
      required_properties:
        Enum.map(
          ~w(slice_transition vector_transition composition preserves_length empty_unchanged shared_core shared_composition index_panic generic_core generic_composition result_core result_composition),
          &("Collections.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert [
             %{
               type: "alloc::vec::Vec<u8>",
               status: :modelled,
               implementation_verified: false,
               first_party: false
             },
             %{
               type: "core::result::Result",
               status: :audited_erasure,
               implementation_verified: false,
               first_party: false
             }
           ] = result.verification.structural_drops

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract and
                 &1.theorem == "Collections.Properties.composition")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract and
                 &1.theorem == "Collections.Properties.generic_composition")
           )

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "Standard Vec Deref shared slice-view model")
           )

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract and
                 &1.theorem == "Collections.Properties.result_composition")
           )

    reject_metadata(result.extraction)

    repeated = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok, cached: true}] = repeated.reports
    export = Path.join(tmp, "collections.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["Collections.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(workspace, "core/src/collections.rs")
    original = File.read!(source)
    changed = String.replace(original, "input[0] = value;", "input[0] = 0;")
    assert changed != original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    # An element-independent observation must be linked to the actual implementation.
    changed = String.replace(original, "input.values.len()", "input.values.len() + 1")
    refute changed == original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    changed = String.replace(original, "input.is_ok()", "!input.is_ok()")
    refute changed == original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    # A wrong shared view must invalidate its own universal length contract too.
    changed = String.replace(original, "(slice.len(), input)", "(slice.len() + 1, input)")
    refute changed == original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end
  end

  @tag tmp_dir: "process-#{System.pid()}"
  test "does not erase a vector's observable first-party element destructor", %{tmp_dir: tmp} do
    workspace = workspace(tmp)
    source = Path.join(workspace, "core/src/collections.rs")

    File.write!(
      source,
      File.read!(source) <>
        """
        pub struct DropByte;
        impl Drop for DropByte {
            fn drop(&mut self) { panic!("observable destructor"); }
        }
        pub fn discard(_values: Vec<DropByte>) {}
        pub fn discard_result(_value: Result<u64, DropByte>) {}
        """
    )

    caller = Path.join(workspace, "analysis/src/lib.rs")

    File.write!(
      caller,
      File.read!(caller) <>
        """
        pub fn discard(values: Vec<experiment_core::collections::DropByte>) {
            experiment_core::collections::discard(values);
        }
        pub fn discard_result(value: Result<u64, experiment_core::collections::DropByte>) {
            experiment_core::collections::discard_result(value);
        }
        """
    )

    context =
      Lynx.Rust.Cargo.build!(workspace, "experiment-analysis", Path.join(tmp, "build"), [])

    for {root, diagnostic} <- [
          {"discard", ~r/structural drop erasure rejected/},
          {"discard_result", ~r/Result drop/}
        ] do
      assert_raise CompileError, diagnostic, fn ->
        Lynx.Rust.Extraction.run!(
          context,
          @tools,
          ["experiment_analysis::" <> root],
          Path.join(tmp, "proofs"),
          "Rejected.Extraction",
          mir: :elaborated
        )
      end
    end
  end

  defp workspace(tmp) do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@workspace, entry), Path.join(workspace, entry))

    workspace
  end

  defp reject_metadata(extraction) do
    audit = extraction.audit
    models = Map.values(audit.external_calls)
    assert Enum.all?(models, &(&1.implementation_verified == false))
    view = Enum.find(models, &String.ends_with?(&1.rust_name, "as_mut_slice"))
    assert %{keep_params: [true, false]} = view

    names =
      JSON.decode!(
        File.read!(Path.join(extraction.output, "Collections_Extraction.external-types.json"))
      )

    assert Enum.any?(names["functions"], &(&1["keep_params"] == [true, false]))
    index = Enum.find(models, &String.ends_with?(&1.rust_name, "::index_mut"))
    bad = put_in(index.function, ["src", "TraitImpl", "item_id"], 4)
    assert CallModels.resolve([bad], audit.translated, audit.references, []) == %{}

    document = File.read!(extraction.llbc) |> JSON.decode!()
    declarations = document["translated"]["type_decls"]

    allocator =
      Enum.find_index(
        declarations,
        &(&1 &&
            &1["item_meta"]["name"] ==
              Enum.map(~w(alloc alloc Global), fn part -> %{"Ident" => [part, 0]} end))
      )

    refute is_nil(allocator)

    bad_allocator =
      put_in(document, ["translated", "type_decls", Access.at(allocator), "item_meta", "name"], [
        %{"Ident" => ["CustomAllocator", 0]}
      ])

    assert_raise CompileError, ~r/unsupported Vec::len: only the standard Global allocator/, fn ->
      LLBC.audit!(bad_allocator, audit.first_party)
    end

    bad_element = change_drop_elements(document)
    assert_raise CompileError, ~r/Vec drop/, fn -> LLBC.audit!(bad_element, audit.first_party) end

    {id, _} =
      Enum.find(audit.drops.erasures, fn {_, model} ->
        model.type == "alloc::vec::Vec<u8>"
      end)

    position = Enum.find_index(document["translated"]["fun_decls"], &(&1 && &1["def_id"] == id))

    bad_signature =
      put_in(
        document,
        ["translated", "fun_decls", Access.at(position), "signature", "is_unsafe"],
        false
      )

    assert_raise CompileError, ~r/Vec drop/, fn ->
      LLBC.audit!(bad_signature, audit.first_party)
    end
  end

  defp change_drop_elements(%{"Drop" => drop} = value),
    do:
      Map.put(
        value,
        "Drop",
        put_in(drop, ["fn_ptr", "generics", "types", Access.at(0)], %{"Scalar" => "Bool"})
      )

  defp change_drop_elements(map) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, change_drop_elements(value)} end)

  defp change_drop_elements(list) when is_list(list), do: Enum.map(list, &change_drop_elements/1)
  defp change_drop_elements(value), do: value
end
