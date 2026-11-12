defmodule Lynx.Rust.RecursiveDropModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{DropModels, LLBC}

  setup do
    fixture =
      Path.expand("../../fixtures/rust_drops/recursive.json", __DIR__)
      |> File.read!()
      |> JSON.decode!()

    %{fixture: fixture, translated: fixture["translated"]}
  end

  defp audit(translated, fixture) do
    consumer = Enum.at(translated["fun_decls"], fixture["consumer"])
    glue = Enum.at(translated["fun_decls"], fixture["glue"])
    refs = LLBC.type_references!(%{"translated" => translated})
    DropModels.audit([consumer], [glue], translated, refs, ["protocol_core", "protocol_analysis"])
  end

  test "checks recursive compiler glue and reports every vector instantiation", ctx do
    assert {:ok, result} = audit(ctx.translated, ctx.fixture)
    report = DropModels.report(result)
    vector = ctx.fixture["vector"]
    glue = ctx.fixture["glue"]

    assert [
             %{
               element_drop_basis: %{kind: :compiler_structural, function_id: ^glue},
               type: "alloc::vec::Vec<protocol_core::Node>",
               implementation_verified: false
             },
             %{element_drop_basis: :primitive_scalar, type: "alloc::vec::Vec<u8>"}
           ] = Enum.filter(report, &(&1.definition_id == vector))

    assert Enum.any?(report, fn entry ->
             entry.definition_id == glue and entry.first_party and
               entry.status == :audited_erasure and not entry.implementation_verified
           end)
  end

  test "rejects incomplete, opaque or observable recursive glue", ctx do
    table = ["fun_decls", Access.at(ctx.fixture["glue"])]
    body = table ++ ["body", "Structured", "body", "statements"]

    for unsupported <- [
          put_in(ctx.translated, table ++ ["body"], "Opaque"),
          put_in(ctx.translated, table ++ ["item_meta", "has_errors"], true),
          put_in(ctx.translated, table ++ ["signature", "is_unsafe"], false),
          put_in(ctx.translated, table ++ ["signature", "output"], %{"Scalar" => "Bool"}),
          update_in(ctx.translated, body, &[%{"kind" => %{"Panic" => %{}}} | &1]),
          update_in(ctx.translated, body, &[%{"kind" => %{"Call" => %{}}} | &1])
        ] do
      assert {:error, _, _} = audit(unsupported, ctx.fixture)
    end
  end

  test "rejects unguarded cycles and altered vector or dictionary identities", ctx do
    glue = Enum.at(ctx.translated["fun_decls"], ctx.fixture["glue"])
    impl = get_in(glue, ["src", "TraitImpl", "impl_ref", "id"])
    refs = LLBC.type_references!(%{"translated" => ctx.translated})
    [input] = Lynx.Rust.CallModels.expand(glue["signature"]["inputs"], refs)
    [_, self, _] = input["Ref"]
    node = self["Adt"]["id"]

    unguarded =
      put_in(
        ctx.translated,
        [
          "type_decls",
          Access.at(node),
          "kind",
          "Enum",
          Access.at(0),
          "fields",
          Access.at(0),
          "ty"
        ],
        self
      )

    assert {:error, _, message} = audit(unguarded, ctx.fixture)
    assert message =~ "unguarded recursive"

    for unsupported <- [
          put_in(ctx.translated, ["fun_decls", Access.at(ctx.fixture["vector"]), "body"], %{}),
          put_in(
            ctx.translated,
            ["fun_decls", Access.at(ctx.fixture["vector"]), "signature", "is_unsafe"],
            false
          ),
          put_in(
            ctx.translated,
            ["trait_impls", Access.at(impl), "methods", Access.at(0), "skip_binder", "id"],
            -1
          ),
          put_in(ctx.translated, ["type_decls", Access.at(6), "item_meta", "name"], [
            %{"Ident" => ["OtherAllocator", 0]}
          ])
        ] do
      assert {:error, _, _} = audit(unsupported, ctx.fixture)
    end
  end
end
