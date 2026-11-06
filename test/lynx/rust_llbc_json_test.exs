defmodule Lynx.Rust.LLBCJsonTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.LLBCJson

  test "keeps compiler drop evidence in the audit while removing only the backend type field" do
    nested = %{"needs_drop" => "ordinary source data"}
    type = %{"def_id" => 7, "kind" => %{"Struct" => []}, "needs_drop" => false}
    document = %{"translated" => %{"type_decls" => [nil, type]}, "body" => nested}

    expected = %{
      "translated" => %{"type_decls" => [nil, Map.delete(type, "needs_drop")]},
      "body" => nested
    }

    assert {^expected, [%{type_id: 7, needs_drop: false}]} =
             LLBCJson.drop_query_metadata!(document)

    for value <- [0, "false", %{}] do
      invalid =
        put_in(document, ["translated", "type_decls"], [Map.put(type, "needs_drop", value)])

      assert_raise ArgumentError, ~r/invalid compiler drop query metadata/, fn ->
        LLBCJson.drop_query_metadata!(invalid)
      end
    end
  end

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

  test "restores removed trait dictionaries without resolving type IDs in the same family" do
    dictionary = %{"kind" => "SelfId", "trait_decl_ref" => %{"id" => 2, "generics" => %{}}}
    binder = fn value -> %{"regions" => [], "outlives" => [], "skip_binder" => value} end

    original = %{
      "removed" => %{"Value" => [7, dictionary]},
      "call" => %{"trait_refs" => [binder.(%{"Deduplicated" => 7})]},
      "type" => %{"Value" => [7, %{"Scalar" => "Bool"}]},
      "type_ref" => %{"Deduplicated" => 7}
    }

    document = Map.delete(original, "removed")
    restored = binder.(%{"Value" => [7, dictionary]})

    assert %{
             "call" => %{"trait_refs" => [^restored]},
             "type" => %{"Value" => [7, %{"Scalar" => "Bool"}]},
             "type_ref" => %{"Deduplicated" => 7}
           } = LLBCJson.restore_trait_references!(document, original)

    assert_raise ArgumentError, ~r/missing LLBC trait reference/, fn ->
      LLBCJson.restore_trait_references!(document, %{})
    end

    assert_raise ArgumentError, ~r/inconsistent LLBC trait-reference/, fn ->
      LLBCJson.restore_trait_references!(
        document,
        Map.put(original, "conflict", %{"Value" => [7, Map.put(dictionary, "kind", "other")]})
      )
    end

    cyclic =
      put_in(dictionary, ["trait_decl_ref", "generics"], %{
        "trait_refs" => [binder.(%{"Deduplicated" => 7})]
      })

    assert_raise ArgumentError, ~r/cyclic LLBC trait reference/, fn ->
      LLBCJson.restore_trait_references!(document, %{"Value" => [7, cyclic]})
    end
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
