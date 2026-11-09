defmodule Lynx.Rustler.TupleConstructorTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.EncoderModels
  @fixture Path.expand("../../fixtures/rustler/tuple_constructor.json", __DIR__)
  # Captured from the pinned Charon extraction of Rustler 0.39.
  @snapshot JSON.decode!(File.read!(@fixture))

  test "admits only the captured safe Rustler constructor signature and lifetime relation" do
    function = @snapshot["function"]
    translated = @snapshot["translated"]

    assert %{
             rust_name: "rustler::types::tuple::make_tuple",
             lean: "Lynx.Rustler.Encoding.makeTuple",
             can_fail: true
           } =
             EncoderModels.resolve(function, translated, %{})

    [env, terms] = function["signature"]["inputs"]

    for changed <- [
          %{function | "body" => "Unstructured"},
          %{function | "src" => %{"TraitImpl" => %{}}},
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "is_variadic"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "output"], env),
          put_in(function, ["signature", "inputs"], [terms, env]),
          put_in(function, ["signature", "inputs"], [
            env,
            put_in(terms, ["Ref", Access.at(2)], "Mut")
          ]),
          put_in(function, ["generics", "outlives"], []),
          update_in(function, ["generics", "regions"], &Enum.reverse/1),
          put_in(function, ["generics", "types"], [%{"index" => 0}]),
          put_in(function, ["generics", "trait_clauses"], [%{}]),
          put_in(function, ["generics", "const_generics"], [%{}])
        ] do
      assert EncoderModels.resolve(changed, translated, %{}) == nil
    end

    for index <- 0..1 do
      changed =
        put_in(translated, ["type_decls", Access.at(index), "item_meta", "name"], [
          %{"Ident" => ["Fake", 0]}
        ])

      assert EncoderModels.resolve(function, changed, %{}) == nil
    end
  end
end
