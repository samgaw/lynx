defmodule Lynx.Rust.ReferenceCopiesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LLBCJson, ReferenceCopies}
  @fixture Path.expand("../../fixtures/rust/borrowed_ownership.json", __DIR__)

  test "eliminates only an adjacent single-dereference compiler temporary" do
    doc = @fixture |> File.read!() |> JSON.decode!()
    assert {lowered, [%{function_id: function, local: local}]} = ReferenceCopies.lower!(doc)
    assert {^lowered, []} = ReferenceCopies.lower!(lowered)
    assert JSON.decode!(LLBCJson.encode_like!(lowered, @fixture)) == lowered
    before = normalize(doc, doc)["translated"]["fun_decls"]
    after_ = normalize(lowered, lowered)["translated"]["fun_decls"]

    for {a, b} <- Enum.zip(before, after_) do
      if a && a["def_id"] == function do
        assert Map.delete(a, "body") == Map.delete(b, "body")
        refute a["body"] == b["body"]
        refute contains_local?(b["body"], local)
      else
        assert a == b
      end
    end
  end

  test "does not propagate retagged, reused, escaping or nonadjacent references" do
    doc = @fixture |> File.read!() |> JSON.decode!()
    {_, [record]} = ReferenceCopies.lower!(doc)

    function =
      Enum.find_index(doc["translated"]["fun_decls"], &(&1 && &1["def_id"] == record.function_id))

    key = [
      "translated",
      "fun_decls",
      Access.at(function),
      "body",
      "Structured",
      "body",
      "statements"
    ]

    statements = get_in(doc, key)
    index = Enum.find_index(statements, &(&1["id"] == record.statement_id))
    use = Enum.at(statements, index + 1)

    for bad <- [
          put_in(
            doc,
            [
              "translated",
              "fun_decls",
              Access.at(function),
              "body",
              "Structured",
              "locals",
              "arg_count"
            ],
            record.local
          ),
          update_in(
            doc,
            key ++ [Access.at(index), "kind", "Assign", Access.at(1), "Use", Access.at(1)],
            fn _ -> "Yes" end
          ),
          update_in(doc, key, &List.insert_at(&1, index + 2, use)),
          update_in(doc, key, &List.insert_at(&1, index + 1, %{"kind" => %{"Call" => %{}}})),
          update_in(doc, key ++ [Access.at(index + 1), "kind"], fn _ ->
            %{
              "Assign" => [
                Enum.at(statements, index)["kind"]["Assign"] |> hd(),
                %{"Use" => [%{"Copy" => %{"kind" => %{"Local" => record.local}}}, "No"]}
              ]
            }
          end)
        ] do
      assert {^bad, []} = ReferenceCopies.lower!(bad)
    end
  end

  defp normalize(doc, original),
    do: doc |> LLBCJson.restore_type_references!(original) |> LLBCJson.restore_spans!(original)

  defp contains_local?(%{"Local" => id}, id), do: true

  defp contains_local?(map, id) when is_map(map),
    do: Enum.any?(Map.values(map), &contains_local?(&1, id))

  defp contains_local?(list, id) when is_list(list), do: Enum.any?(list, &contains_local?(&1, id))
  defp contains_local?(_, _), do: false
end
