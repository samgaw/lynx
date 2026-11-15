defmodule Lynx.Rust.OwnedMutexPayloadTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LLBC, NativeOwnedDrops, ResourceModels}
  @snapshot Path.expand("../../fixtures/rustler/owned_mutex_payload.json", __DIR__)

  setup do
    translated = File.read!(@snapshot) |> JSON.decode!()
    refs = LLBC.type_references!(%{"translated" => translated})

    inner =
      Enum.find(
        translated["type_decls"],
        &(&1["item_meta"]["name"] == path(~w(atomic_core BufferState)))
      )

    outer =
      Enum.find(
        translated["type_decls"],
        &(&1["item_meta"]["name"] == path(~w(atomic_nif SharedBuffer)))
      )

    helper =
      Enum.find(
        translated["fun_decls"],
        &(&1["item_meta"]["name"] == inner["item_meta"]["name"] ++ path(~w(drop_owned)))
      )

    %{translated: translated, refs: refs, inner: inner, outer: outer, helper: helper}
  end

  test "links the actual first-party vector cleanup before admitting mutex cleanup", c do
    assert %{"def_id" => id} =
             NativeOwnedDrops.vector_cleanup_for(type(c.inner), c.translated, c.refs)

    assert id == c.helper["def_id"]

    assert %{"body" => %{"Structured" => _}} =
             NativeOwnedDrops.function_for(type(c.outer), c.translated, c.refs)

    refute NativeOwnedDrops.vector_cleanup_for(type(c.outer), c.translated, c.refs)
    refute NativeOwnedDrops.vector_cleanup_for(%{"Scalar" => "Bool"}, c.translated, c.refs)
  end

  test "rejects absent, opaque and changed cleanup instead of accepting a default", c do
    for helper <- [
          Map.put(c.helper, "body", "Opaque"),
          put_in(c.helper, ["signature", "is_unsafe"], true),
          put_in(c.helper, ["body", "Structured", "body", "statements"], [
            %{"kind" => %{"Call" => %{}}}
          ])
        ] do
      translated =
        update_in(c.translated, ["fun_decls"], fn fs ->
          Enum.map(fs, &if(&1["def_id"] == c.helper["def_id"], do: helper, else: &1))
        end)

      refute NativeOwnedDrops.vector_cleanup_for(type(c.inner), translated, c.refs)
      refute NativeOwnedDrops.function_for(type(c.outer), translated, c.refs)
    end

    translated =
      update_in(
        c.translated,
        ["fun_decls"],
        &Enum.reject(&1, fn f -> f["def_id"] == c.helper["def_id"] end)
      )

    refute NativeOwnedDrops.vector_cleanup_for(type(c.inner), translated, c.refs)
    refute NativeOwnedDrops.function_for(type(c.outer), translated, c.refs)
  end

  test "requires exact Global destruction and supported vector fields", c do
    helper =
      update_in(c.helper, ["body", "Structured", "body", "statements"], fn statements ->
        Enum.map(statements, fn statement ->
          case statement["kind"] do
            %{"Drop" => _} ->
              put_in(statement, ["kind", "Drop", "fn_ptr", "generics", "types", Access.at(1)], %{
                "Scalar" => "Bool"
              })

            _ ->
              statement
          end
        end)
      end)

    translated =
      update_in(c.translated, ["fun_decls"], fn fs ->
        Enum.map(fs, &if(&1["def_id"] == c.helper["def_id"], do: helper, else: &1))
      end)

    refute NativeOwnedDrops.vector_cleanup_for(type(c.inner), translated, c.refs)
    refute NativeOwnedDrops.function_for(type(c.outer), translated, c.refs)
  end

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp type(decl),
    do: %{
      "Adt" => %{"id" => decl["def_id"], "builtin" => nil, "generics" => ResourceModels.args([])}
    }
end
