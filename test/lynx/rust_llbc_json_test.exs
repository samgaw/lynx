defmodule Lynx.Rust.LLBCJsonTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.LLBCJson

  test "restores source spans removed with cleanup without crossing deduplication families" do
    span = %{
      "data" => %{
        "file_id" => 0,
        "beg" => %{"line" => 7, "col" => 0},
        "end" => %{"line" => 7, "col" => 2}
      },
      "generated_from_span" => nil
    }

    original = %{
      "removed" => %{"span" => %{"Value" => [7, span]}},
      "body" => %{"span" => %{"Deduplicated" => 7}},
      "type" => %{"Value" => [7, %{"Scalar" => "Bool"}]},
      "type_ref" => %{"Deduplicated" => 7}
    }

    document = Map.delete(original, "removed")

    assert %{
             "body" => %{"span" => %{"Untagged" => ^span}},
             "type" => %{"Value" => [7, %{"Scalar" => "Bool"}]},
             "type_ref" => %{"Deduplicated" => 7}
           } = LLBCJson.restore_spans!(document, original)

    assert_raise ArgumentError, ~r/missing LLBC span/, fn ->
      LLBCJson.restore_spans!(
        put_in(document, ["body", "span"], %{"Deduplicated" => 8}),
        original
      )
    end

    assert_raise ArgumentError, ~r/inconsistent LLBC span/, fn ->
      LLBCJson.restore_spans!(
        document,
        Map.put(original, "conflict", %{"span" => %{"Value" => [7, %{}]}})
      )
    end
  end

  @tag :tmp_dir
  test "preserves record order while changing values and adding typed records", %{tmp_dir: tmp} do
    path = Path.join(tmp, "source.json")
    File.write!(path, ~s({"z":{"third":3,"first":1},"a":[{"index":0,"name":null,"ty":true}]}))

    document = %{
      "z" => %{"third" => 4, "first" => 2},
      "a" => [
        %{"index" => 0, "name" => nil, "ty" => true},
        %{"index" => 1, "name" => nil, "ty" => false}
      ]
    }

    encoded = LLBCJson.encode_like!(document, path)
    assert JSON.decode!(encoded) == document
    assert String.starts_with?(encoded, ~s({"z":{"third":4,"first":2},"a":))
    assert String.contains?(encoded, ~s({"index":1,"name":null,"ty":false}))
  end

  @tag :tmp_dir
  test "rejects ambiguous schemas for a new record rather than guessing field order", %{
    tmp_dir: tmp
  } do
    path = Path.join(tmp, "source.json")
    File.write!(path, ~s({"one":{"a":1,"b":2},"two":{"b":3,"a":4},"three":null}))
    document = JSON.decode!(File.read!(path)) |> Map.put("three", %{"a" => 5, "b" => 6})

    assert_raise ArgumentError, ~r/ambiguous LLBC record/, fn ->
      LLBCJson.encode_like!(document, path)
    end
  end
end
