defmodule Lynx.Rust.VectorSplitsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CollectionModels, LLBC, VectorSplits}
  @snapshot Path.expand("../../fixtures/rustler/vector_split.json", __DIR__)

  setup do
    document = File.read!(@snapshot) |> JSON.decode!()
    t = document["translated"]
    refs = LLBC.type_references!(document)

    function =
      Enum.find(
        t["fun_decls"],
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["split_off", 0]})
      )

    caller =
      Enum.find(
        t["fun_decls"],
        &(&1 && &1["item_meta"]["name"] == path(~w(atomic_core frames split_buffer)))
      )

    call =
      Enum.find(
        caller["body"]["Structured"]["body"]["statements"],
        &match?(%{"Call" => _}, &1["kind"])
      )

    args = call["kind"]["Call"]["call"]["func"]["Regular"]["generics"]
    %{document: document, t: t, refs: refs, function: function, caller: caller, args: args}
  end

  test "admission retains panic behavior and validates the standard allocator dictionary", c do
    assert %{can_fail: true, native_cutoff_only: false, keep_trait_clauses: [false]} =
             VectorSplits.resolve(c.function, c.t, c.refs)

    assert VectorSplits.valid_call?(c.args, c.t, c.refs)

    refute MapSet.member?(
             Lynx.Rust.NativeBorrows.nonpanicking_calls([c.caller], %{
               c.function["def_id"] => VectorSplits.resolve(c.function, c.t, c.refs)
             }),
             c.caller["def_id"]
           )

    refute VectorSplits.resolve(put_in(c.function, ["signature", "is_unsafe"], true), c.t, c.refs)

    refute VectorSplits.resolve(
             put_in(c.function, ["signature", "output"], %{"Scalar" => "Bool"}),
             c.t,
             c.refs
           )

    refute VectorSplits.resolve(
             put_in(c.function, ["generics", "trait_clauses"], []),
             c.t,
             c.refs
           )
  end

  test "rejects changed types, allocator callbacks and trait correspondence", c do
    refute VectorSplits.valid_call?(%{c.args | "trait_refs" => []}, c.t, c.refs)

    refute VectorSplits.valid_call?(
             put_in(c.args, ["types", Access.at(0)], %{"Scalar" => "Bool"}),
             c.t,
             c.refs
           )

    refute VectorSplits.valid_call?(
             put_in(c.args, ["types", Access.at(1)], %{"Scalar" => "Bool"}),
             c.t,
             c.refs
           )

    clone =
      Enum.find(
        c.t["fun_decls"],
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["clone", 0]} &&
            &1["body"] == "Opaque" && &1["signature"]["is_unsafe"] == false)
      )

    for changed <- [
          put_in(clone, ["signature", "is_unsafe"], true),
          put_in(clone, ["src", "TraitImpl", "item_id"], 1),
          put_in(clone, ["item_meta", "name"], path(~w(unapproved clone)))
        ] do
      t =
        update_in(
          c.t,
          ["fun_decls"],
          &Enum.map(&1, fn f -> if f == clone, do: changed, else: f end)
        )

      refute VectorSplits.valid_call?(c.args, t, c.refs)
    end
  end

  test "never prunes split panic cleanup as a nonpanicking vector operation", c do
    {document, records} =
      CollectionModels.prune_nonpanicking_calls!(c.document, ~w(atomic_core atomic_analysis))

    after_function =
      Enum.find(document["translated"]["fun_decls"], &(&1 && &1["def_id"] == c.caller["def_id"]))

    before_call =
      Enum.find(
        c.caller["body"]["Structured"]["body"]["statements"],
        &match?(%{"Call" => _}, &1["kind"])
      )

    after_call =
      Enum.find(
        after_function["body"]["Structured"]["body"]["statements"],
        &match?(%{"Call" => _}, &1["kind"])
      )

    assert after_call["kind"]["Call"]["on_unwind"] == before_call["kind"]["Call"]["on_unwind"]
    refute Enum.any?(records, &(&1.function == c.function["def_id"]))
  end

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
