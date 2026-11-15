defmodule Lynx.Rust.NestedMutexPayloadTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LLBC, NativeOwnedDrops, ResourceModels}
  @snapshot Path.expand("../../fixtures/rustler/nested_mutex_payload.json", __DIR__)

  setup do
    translated = File.read!(@snapshot) |> JSON.decode!()
    refs = LLBC.type_references!(%{"translated" => translated})
    %{translated: translated, refs: refs}
  end

  # Compiler snapshot: ReceiveState { buffer: BufferState { bytes: Vec<u8> }, accepted: u64 }.
  # The leaf Vec retains its Global allocator in the actual drop function pointer.
  test "admits nested cross-crate vector ownership using both captured helpers", c do
    assert %{"def_id" => 22} =
             NativeOwnedDrops.vector_cleanup_for(payload(), c.translated, c.refs)

    assert %{"def_id" => 22} = NativeOwnedDrops.function_for(payload(), c.translated, c.refs)
  end

  test "rejects missing, opaque and observable nested cleanup", c do
    for id <- [24, 25], change <- [:missing, :opaque, :call] do
      translated =
        update_in(c.translated, ["fun_decls"], fn functions ->
          Enum.flat_map(functions, fn
            %{"def_id" => ^id} = function ->
              case change do
                :missing ->
                  []

                :opaque ->
                  [Map.put(function, "body", "Opaque")]

                :call ->
                  [
                    put_in(function, ["body", "Structured", "body", "statements"], [
                      %{"kind" => %{"Call" => %{}}}
                    ])
                  ]
              end

            function ->
              [function]
          end)
        end)

      refute NativeOwnedDrops.vector_cleanup_for(payload(), translated, c.refs)
    end
  end

  test "rejects a wrong nested drop dictionary and cyclic owning types", c do
    translated =
      update_in(c.translated, ["fun_decls"], fn functions ->
        Enum.map(functions, fn
          %{"def_id" => 22} = function ->
            update_in(function, ["body", "Structured", "body", "statements"], fn statements ->
              Enum.map(statements, fn statement ->
                case statement["kind"] do
                  %{"Drop" => _} ->
                    put_in(statement, ["kind", "Drop", "fn_ptr", "kind", "Fun"], 26)

                  _ ->
                    statement
                end
              end)
            end)

          function ->
            function
        end)
      end)

    refute NativeOwnedDrops.vector_cleanup_for(payload(), translated, c.refs)

    cyclic =
      update_in(c.translated, ["type_decls"], fn types ->
        Enum.map(types, fn
          %{"def_id" => 8} = type ->
            put_in(type, ["kind", "Struct", Access.at(0), "ty"], payload())

          type ->
            type
        end)
      end)

    refute NativeOwnedDrops.vector_cleanup_for(payload(), cyclic, c.refs)
  end

  defp payload,
    do: %{"Adt" => %{"id" => 6, "builtin" => nil, "generics" => ResourceModels.args([])}}
end
