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

  test "constructors match the actual standard types, signatures and lifetime relationships" do
    context = Map.put(type("Context", [%{"index" => 0}]), "def_id", 6)
    waker = Map.put(type("Waker", []), "def_id", 7)
    translated = %{"type_decls" => [context, waker]}

    empty = %{
      "types" => [],
      "regions" => [],
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => []
    }

    args = fn regions ->
      %{"regions" => regions, "types" => [], "const_generics" => [], "trait_refs" => []}
    end

    adt = fn id, regions ->
      %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args.(regions)}}
    end

    region = %{"Var" => %{"Free" => 0}}
    binder = %{"Var" => %{"Bound" => [0, 0]}}

    make = fn name, parent, generics, inputs, output ->
      %{
        "src" => "Normal",
        "body" => "Opaque",
        "generics" => generics,
        "signature" => %{
          "is_unsafe" => false,
          "is_variadic" => false,
          "abi" => "Rust",
          "inputs" => inputs,
          "output" => output
        },
        "item_meta" => %{
          "name" =>
            Enum.map(~w(core task wake), &%{"Ident" => [&1, 0]}) ++
              [
                %{"Impl" => %{"Ty" => %{"kind" => "InherentImplBlock", "skip_binder" => parent}}},
                %{"Ident" => [name, 0]}
              ]
        }
      }
    end

    noop = make.("noop", adt.(7, []), empty, [], %{"Ref" => ["Static", adt.(7, []), "Shared"]})

    from =
      make.(
        "from_waker",
        adt.(6, [binder]),
        Map.put(empty, "regions", [%{"index" => 0}]),
        [%{"Ref" => [region, adt.(7, []), "Shared"]}],
        adt.(6, [region])
      )

    assert %{native_wake_operation: :noop, can_fail: false} =
             FutureModels.resolve(noop, translated, %{})

    assert %{native_wake_operation: :from_waker, can_fail: false} =
             FutureModels.resolve(from, translated, %{})

    for function <- [noop, from],
        bad <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "output"], adt.(7, [])),
          put_in(function, ["signature", "inputs"], [adt.(7, [])]),
          put_in(function, ["generics", "types"], [%{}]),
          Map.put(function, "body", %{"Structured" => %{}})
        ] do
      refute FutureModels.resolve(bad, translated, %{})
    end
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
