defmodule Lynx.Rust.ResultDropTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{DropModels, LLBC}

  setup do
    document =
      Path.expand("../../fixtures/rust/result_drop.json", __DIR__)
      |> File.read!()
      |> JSON.decode!()

    translated = document["translated"]

    function =
      Enum.find(translated["fun_decls"], fn item ->
        item &&
          item["item_meta"]["name"] ==
            Enum.map(~w(experiment_core collections result_is_ok), &%{"Ident" => [&1, 0]})
      end)

    glue =
      Enum.find(translated["fun_decls"], fn item ->
        item && List.last(item["item_meta"]["name"]) == %{"Builtin" => ["DropGlue", 0]}
      end)

    %{translated: translated, function: function, glue: glue}
  end

  test "checks actual generic Result glue at concrete payload types", ctx do
    assert {:ok, %{erasures: entries}} = audit(ctx.translated, ctx.function)

    assert [
             %{
               type: "core::result::Result",
               status: :audited_erasure,
               implementation_verified: false,
               first_party: false,
               label: label
             }
           ] = Map.values(entries)

    assert label =~ "logical String deallocation"
    assert label =~ "unverified"
  end

  test "requires actual glue, its unsafe Rust signature and exact dictionary", ctx do
    for replacement <- [
          Map.put(ctx.glue, "body", "Opaque"),
          put_in(ctx.glue, ["signature", "abi"], "C"),
          put_in(ctx.glue, ["signature", "is_unsafe"], false),
          put_in(ctx.glue, ["src", "TraitImpl", "item_id"], 1),
          put_in(ctx.glue, ["item_meta", "has_errors"], true),
          put_in(ctx.glue, ["generics", "trait_clauses"], [%{}])
        ] do
      assert {:error, _, _} =
               audit(replace(ctx.translated, "fun_decls", ctx.glue, replacement), ctx.function)
    end
  end

  test "rejects calls or assertions even after an administrative return", ctx do
    for kind <- [%{"Call" => %{}}, %{"Assert" => %{}}, "Abort"] do
      bad =
        update_in(
          ctx.glue,
          ["body", "Structured", "body", "statements"],
          &(&1 ++ [%{"kind" => kind}])
        )

      assert {:error, _, message} =
               audit(replace(ctx.translated, "fun_decls", ctx.glue, bad), ctx.function)

      assert message =~ "observable or unsupported behavior"
    end
  end

  test "rejects unapproved owned payloads and inconsistent Result layouts", ctx do
    string =
      Enum.find(
        ctx.translated["type_decls"],
        &(&1 &&
            &1["item_meta"]["name"] ==
              Enum.map(~w(alloc string String), fn n -> %{"Ident" => [n, 0]} end))
      )

    bad = put_in(string, ["item_meta", "name"], [%{"Ident" => ["OwningError", 0]}])

    assert {:error, _, _} =
             audit(replace(ctx.translated, "type_decls", string, bad), ctx.function)

    result =
      Enum.find(
        ctx.translated["type_decls"],
        &(&1 &&
            &1["item_meta"]["name"] ==
              Enum.map(~w(core result Result), fn n -> %{"Ident" => [n, 0]} end))
      )

    bad =
      put_in(result, ["kind", "Enum", Access.at(1), "fields", Access.at(0), "ty"], %{
        "Scalar" => "Bool"
      })

    assert {:error, _, _} =
             audit(replace(ctx.translated, "type_decls", result, bad), ctx.function)
  end

  test "does not treat an arbitrary untracked trait as a payload destructor", ctx do
    changed = alter_dictionary(ctx.translated)
    refute changed == ctx.translated
    assert {:error, _, _} = audit(changed, ctx.function)
  end

  test "reuses the upstream shared Result observer with an exact interface", ctx do
    method = observer(ctx)
    refs = LLBC.type_references!(%{"translated" => ctx.translated})

    assert %{
             builtin: true,
             can_fail: true,
             lift: false,
             lean: "Aeneas.Std.core.result.Result.is_ok",
             implementation_verified: false
           } =
             Lynx.Rust.CallModels.resolve([method], ctx.translated, refs, [])[method["def_id"]]
  end

  test "rejects altered observer ABI, payload borrow and result type", ctx do
    method = observer(ctx)
    refs = LLBC.type_references!(%{"translated" => ctx.translated})
    [input] = Lynx.Rust.CallModels.expand(method["signature"]["inputs"], refs)
    mutable = put_in(input, ["Ref", Access.at(2)], "Mut")

    for bad <- [
          put_in(method, ["signature", "abi"], "C"),
          put_in(method, ["signature", "inputs"], [mutable]),
          put_in(method, ["signature", "output"], %{
            "Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}
          }),
          put_in(method, ["generics", "trait_clauses"], [%{}])
        ] do
      assert %{} == Lynx.Rust.CallModels.resolve([bad], ctx.translated, refs, [])
    end
  end

  defp observer(ctx),
    do:
      Enum.find(ctx.translated["fun_decls"], fn f ->
        f && List.last(f["item_meta"]["name"]) == %{"Ident" => ["is_ok", 0]}
      end)

  defp alter_dictionary(%{"builtin_data" => "UntrackedDestruct"} = map),
    do: Map.put(map, "builtin_data", "UnapprovedDrop")

  defp alter_dictionary(map) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, alter_dictionary(v)} end)

  defp alter_dictionary(list) when is_list(list), do: Enum.map(list, &alter_dictionary/1)
  defp alter_dictionary(value), do: value

  defp audit(translated, function) do
    refs = LLBC.type_references!(%{"translated" => translated})
    DropModels.audit([function], [], translated, refs, ["experiment_core", "experiment_analysis"])
  end

  defp replace(translated, section, old, replacement) do
    Map.update!(
      translated,
      section,
      &Enum.map(&1, fn
        ^old -> replacement
        other -> other
      end)
    )
  end
end
