defmodule Lynx.Rust.OwnedStringModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.OwnedStringModels
  @snapshot Path.expand("../../fixtures/rustler/owned_strings.json", __DIR__)

  setup do
    %{"functions" => functions, "translated" => translated} =
      JSON.decode!(File.read!(@snapshot))

    %{functions: functions, translated: translated}
  end

  test "admits the compiled owned conversions and append signatures", ctx do
    ops =
      for function <- ctx.functions do
        assert %{builtin: false, owned_string_op: operation, label: label} =
                 OwnedStringModels.resolve(function, ctx.translated, %{})

        assert label =~ "remain unverified"
        operation
      end

    assert Enum.sort(ops) == ~w(errorIntoBytes fromUtf8 intoBytes pushStr)
  end

  test "String result recognition requires compiler identity rather than its spelling", ctx do
    type =
      Enum.find(ctx.translated["type_decls"], &(&1 && &1["item_meta"]["lang_item"] == "String"))

    id = type["def_id"]

    value = %{
      "Adt" => %{"id" => id, "builtin" => nil, "generics" => Lynx.Rust.ResourceModels.args([])}
    }

    assert OwnedStringModels.type?(value, ctx.translated, %{})

    assert Lynx.Rust.LLBC.nif_type!(value, %{translated: ctx.translated, references: %{}}) ==
             "string"

    for changed <- [
          put_in(type, ["item_meta", "lang_item"], nil),
          Map.put(type, "kind", %{"Struct" => []}),
          put_in(type, ["item_meta", "name"], [%{"Ident" => ["String", 0]}])
        ] do
      translated =
        Map.update!(ctx.translated, "type_decls", fn types ->
          Enum.map(types, fn
            %{"def_id" => ^id} -> changed
            other -> other
          end)
        end)

      refute OwnedStringModels.type?(value, translated, %{})

      assert_raise ArgumentError, fn ->
        Lynx.Rust.LLBC.nif_type!(value, %{translated: translated, references: %{}})
      end
    end

    assert [boundary] =
             Lynx.Rustler.Bindings.codec_boundaries(
               %{bindings: [%{"result" => %{"option" => %{"result" => ["string", "u8"]}}}]},
               "0.39.0"
             )

    assert boundary =~ "String Encoder model"
    assert boundary =~ "unverified"

    assert [] ==
             Lynx.Rustler.Bindings.codec_boundaries(
               %{bindings: [%{"result" => %{"native" => ["String"]}}]},
               "0.39.0"
             )
  end

  test "requires the exact standard owned-error fields and borrowed append lifetimes", ctx do
    error =
      Enum.find(
        ctx.translated["type_decls"],
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["FromUtf8Error", 0]})
      )

    id = error["def_id"]

    for changed <- [
          Map.put(error, "kind", "Opaque"),
          update_in(error, ["kind", "Struct"], &Enum.reverse/1),
          put_in(error, ["kind", "Struct", Access.at(0), "ty"], %{"Scalar" => "Bool"}),
          put_in(error, ["generics", "types"], [%{"index" => 0}])
        ] do
      translated =
        Map.update!(ctx.translated, "type_decls", fn types ->
          Enum.map(types, fn
            %{"def_id" => ^id} -> changed
            type -> type
          end)
        end)

      for function <- ctx.functions,
          operation = OwnedStringModels.resolve(function, ctx.translated, %{}).owned_string_op,
          operation in ~w(fromUtf8 errorIntoBytes) do
        refute OwnedStringModels.resolve(function, translated, %{})
      end
    end

    append =
      Enum.find(
        ctx.functions,
        &(List.last(&1["item_meta"]["name"]) == %{"Ident" => ["push_str", 0]})
      )

    for changed <- [
          put_in(append, ["generics", "regions"], []),
          put_in(append, ["signature", "inputs", Access.at(0), "Ref", Access.at(2)], "Shared"),
          put_in(append, ["signature", "inputs", Access.at(1), "Ref", Access.at(0)], %{
            "Var" => %{"Free" => 0}
          })
        ] do
      refute OwnedStringModels.resolve(changed, ctx.translated, %{})
    end
  end
end
