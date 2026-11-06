defmodule Lynx.Rust.FutureModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{Extraction, FutureModels}

  test "stateful polling is an explicit runtime mode" do
    assert_raise ArgumentError, ~r/requires runtime execution/, fn ->
      Extraction.run!(%{}, "/unused", ["probe::poll"], "/unused", "Probe.Extraction",
        futures: :polling
      )
    end
  end

  test "waker type models reject duplicate, opaque-shape and generic mismatches" do
    context = type("Context", [%{"index" => 0}])
    waker = type("Waker", [])
    translated = %{"type_decls" => [nil, context, waker]}
    assert ^context = FutureModels.type(translated, "Context")
    assert ^waker = FutureModels.type(translated, "Waker")

    for bad <- [
          Map.put(waker, "kind", %{"Struct" => []}),
          put_in(waker, ["generics", "regions"], [%{}]),
          put_in(waker, ["generics", "types"], [%{}])
        ] do
      refute FutureModels.type(%{"type_decls" => [context, bad]}, "Waker")
    end

    refute FutureModels.type(%{"type_decls" => [waker, waker]}, "Waker")
  end

  defp type(name, regions) do
    %{
      "src" => "Normal",
      "kind" => "Opaque",
      "item_meta" => %{"name" => Enum.map(["core", "task", "wake", name], &%{"Ident" => [&1, 0]})},
      "generics" => %{
        "types" => [],
        "regions" => regions,
        "const_generics" => [],
        "trait_clauses" => [],
        "trait_type_constraints" => []
      }
    }
  end
end
