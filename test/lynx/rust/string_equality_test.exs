defmodule Lynx.Rust.StringEqualityTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LibraryHelpers, LLBC}
  @snapshot Path.expand("../../fixtures/rustler/string_equality.json", __DIR__)

  setup do
    document = JSON.decode!(File.read!(@snapshot))
    document = put_in(document, ["translated", "files"], [])
    t = document["translated"]
    helper = Enum.find(t["fun_decls"], &(&1 && LibraryHelpers.selected?(&1, t)))
    %{document: document, t: t, helper: helper}
  end

  test "retains the actual standard equality body with complete comparison dependencies", ctx do
    assert %{"body" => %{"Structured" => _}} = ctx.helper

    assert %{library_helpers: helpers} =
             LLBC.audit!(ctx.document, ~w(experiment_analysis experiment_core))

    assert ctx.helper["def_id"] in helpers
    assert "core::str::traits::_::eq" in LibraryHelpers.includes(%{sysroot: %{path: "full"}})
    refute "core::str::traits::_::eq" in LibraryHelpers.includes()
  end

  test "rejects altered signatures and missing or mismatched implementation bindings", ctx do
    for helper <- [
          put_in(ctx.helper, ["signature", "is_unsafe"], true),
          put_in(ctx.helper, ["signature", "abi"], "C"),
          put_in(ctx.helper, ["signature", "inputs"], []),
          put_in(ctx.helper, ["signature", "output"], %{"Scalar" => "Never"}),
          Map.put(ctx.helper, "body", "Opaque"),
          put_in(ctx.helper, ["src", "TraitImpl", "trait_ref", "id"], 999),
          put_in(ctx.helper, ["src", "TraitImpl", "impl_ref", "id"], 999)
        ] do
      refute LibraryHelpers.selected?(helper, ctx.t)
    end

    id = ctx.helper["src"]["TraitImpl"]["impl_ref"]["id"]
    impl = Enum.find(ctx.t["trait_impls"], &(&1 && &1["def_id"] == id))

    for changed <- [
          Map.put(impl, "is_unsafe", true),
          Map.put(impl, "is_negative", true),
          Map.put(impl, "methods", []),
          put_in(impl, ["generics", "outlives"], [%{}])
        ] do
      altered =
        Map.update!(
          ctx.t,
          "trait_impls",
          &Enum.map(&1, fn row -> if row == impl, do: changed, else: row end)
        )

      refute LibraryHelpers.selected?(ctx.helper, altered)
    end
  end

  test "rejects absent comparison methods instead of assuming their behavior", ctx do
    ne =
      Enum.find(ctx.t["fun_decls"], fn f ->
        f && f["item_meta"]["name"] == Enum.map(~w(core cmp PartialEq ne), &%{"Ident" => [&1, 0]})
      end)

    assert ne

    changed =
      update_in(ctx.document, ["translated", "fun_decls"], &Enum.reject(&1, fn f -> f == ne end))

    assert_raise CompileError, ~r/captured eq\/ne/, fn ->
      LLBC.audit!(changed, ~w(experiment_analysis experiment_core))
    end
  end
end
