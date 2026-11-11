defmodule Lynx.Rustler.AtomModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC}
  alias Lynx.Rustler.{AtomModels, DecoderDispatch, DecoderModels}
  @snapshot Path.expand("../../fixtures/rustler/atom_decoder.json", __DIR__)

  setup do
    doc = JSON.decode!(File.read!(@snapshot))
    t = doc["translated"]
    refs = LLBC.type_references!(doc)
    functions = Enum.reject(t["fun_decls"], &is_nil/1)

    eq =
      Enum.find(
        functions,
        &(&1["body"] == "Opaque" and List.last(&1["item_meta"]["name"]) == %{"Ident" => ["eq", 0]})
      )

    ne = Enum.find(functions, &(&1["item_meta"]["name"] == path(~w(core cmp PartialEq ne))))

    decoder =
      Enum.find(functions, fn f ->
        match?(
          [
            %{"Ident" => ["rustler", 0]},
            %{"Ident" => ["types", 0]},
            %{"Ident" => ["atom", 0]},
            _,
            %{"Ident" => ["decode", 0]}
          ],
          f["item_meta"]["name"]
        )
      end)

    body =
      Enum.find(
        functions,
        &match?(
          [%{"Ident" => ["experiment_nif", 0]}, _, %{"Ident" => ["decode", 0]}],
          &1["item_meta"]["name"]
        )
      )

    models = CallModels.resolve(functions, t, refs, [:rustler_decoders, :rustler_encoders])

    %{
      translated: t,
      refs: refs,
      eq: eq,
      ne: ne,
      decoder: decoder,
      body: body,
      models: models
    }
  end

  test "Atom decoding validates its actual Decoder implementation and nominal result", ctx do
    assert %{lean: "Lynx.Rustler.Decoding.atom", decoder_trait: _, can_fail: true} =
             DecoderModels.resolve(ctx.decoder, ctx.translated, ctx.refs)

    for changed <- [
          put_in(ctx.decoder, ["signature", "abi"], "C"),
          put_in(ctx.decoder, ["signature", "is_unsafe"], true),
          put_in(ctx.decoder, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.decoder, ["src", "TraitImpl", "reuses_default"], true),
          put_in(ctx.decoder, ["generics", "types"], [%{"index" => 0}])
        ],
        do: assert(is_nil(DecoderModels.resolve(changed, ctx.translated, ctx.refs)))
  end

  test "validates both equality operands, shared borrows and method identity", ctx do
    assert %{atom_eq: true, can_fail: true, lean: "Lynx.Rustler.atomEq"} =
             AtomModels.resolve(ctx.eq, ctx.translated, ctx.refs)

    [left, right] = CallModels.expand(ctx.eq["signature"]["inputs"], ctx.refs)

    for changed <- [
          put_in(ctx.eq, ["signature", "abi"], "C"),
          put_in(ctx.eq, ["signature", "inputs"], [
            put_in(left, ["Ref", Access.at(2)], "Mut"),
            right
          ]),
          put_in(ctx.eq, ["signature", "output"], %{
            "Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}
          }),
          put_in(ctx.eq, ["src", "TraitImpl", "item_id"], 1),
          put_in(ctx.eq, ["item_meta", "has_errors"], true),
          put_in(ctx.eq, ["generics", "trait_clauses"], [%{}])
        ],
        do: assert(is_nil(AtomModels.resolve(changed, ctx.translated, ctx.refs)))
  end

  test "uses the existing default inequality with a closed concrete equality dependency", ctx do
    assert %{builtin: true, atom_ne: true, lean: "Aeneas.Std.core.cmp.PartialEq.ne.trait_default"} =
             AtomModels.resolve(ctx.ne, ctx.translated, ctx.refs)

    assert {:ok, %{dependencies: deps}} =
             DecoderDispatch.audit([ctx.body], ctx.models, ctx.translated, ctx.refs)

    assert ctx.eq["def_id"] in deps[ctx.body["def_id"]]
    assert ctx.decoder["def_id"] in deps[ctx.body["def_id"]]

    for models <- [
          Map.delete(ctx.models, ctx.eq["def_id"]),
          Map.put(ctx.models, ctx.eq["def_id"], %{atom_eq: false})
        ] do
      assert {:error, _, message} =
               DecoderDispatch.audit([ctx.body], models, ctx.translated, ctx.refs)

      assert message =~ "validated concrete Rustler Atom equality"
    end

    for changed <- [
          put_in(ctx.ne, ["signature", "abi"], "C"),
          put_in(ctx.ne, ["src", "TraitDefault", "item_id"], 0),
          put_in(ctx.ne, ["generics", "outlives"], []),
          put_in(ctx.ne, ["generics", "trait_clauses"], [])
        ],
        do: assert(is_nil(AtomModels.resolve(changed, ctx.translated, ctx.refs)))
  end

  test "rejects a changed standard default-method target", ctx do
    trait = AtomModels.resolve(ctx.ne, ctx.translated, ctx.refs).atom_trait

    changed =
      put_in(
        ctx.translated,
        [
          "trait_decls",
          Access.at(trait),
          "methods",
          Access.at(1),
          "skip_binder",
          "default",
          "id"
        ],
        ctx.ne["def_id"] + 1
      )

    assert is_nil(AtomModels.resolve(ctx.ne, changed, ctx.refs))
  end

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
