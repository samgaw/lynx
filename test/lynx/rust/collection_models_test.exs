defmodule Lynx.Rust.CollectionModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.CallModels

  defp params(count, regions, outlives) do
    %{
      "types" => Enum.map(0..(count - 1), &%{"index" => &1}),
      "regions" => regions,
      "outlives" => outlives,
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => []
    }
  end

  defp example(method) do
    t = %{"TypeVar" => %{"Free" => 0}}
    args = %{"types" => [t], "regions" => [], "const_generics" => [], "trait_refs" => []}
    vector = %{"Adt" => %{"id" => 5, "builtin" => nil, "generics" => args}}
    parent = put_in(vector, ["Adt", "generics", "types"], [%{"TypeVar" => %{"Bound" => [0, 0]}}])

    outlives =
      Enum.map(0..1, fn i ->
        %{
          "regions" => [],
          "outlives" => [],
          "skip_binder" => [
            %{"Lub" => %{"TypeVar" => %{"Free" => i}}},
            %{"Var" => %{"Free" => 0}}
          ]
        }
      end)

    kind = if method == "as_slice", do: "Shared", else: "Mut"
    ref = fn type -> %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, kind]} end

    f = %{
      "def_id" => 1,
      "body" => "Opaque",
      "src" => "Normal",
      "generics" => params(2, [%{"index" => 0}], outlives),
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["alloc", 0]},
          %{"Ident" => ["vec", 0]},
          %{
            "Impl" => %{
              "Ty" => %{
                "kind" => "InherentImplBlock",
                "params" => params(2, [], []),
                "skip_binder" => parent
              }
            }
          },
          %{"Ident" => [method, 0]}
        ]
      },
      "signature" => %{
        "is_unsafe" => false,
        "abi" => "Rust",
        "is_variadic" => false,
        "inputs" => [ref.(vector)],
        "output" => ref.(%{"Slice" => [t, nil]})
      }
    }

    types = %{
      "type_decls" => [
        %{
          "def_id" => 5,
          "generics" => params(1, [], []),
          "item_meta" => %{"name" => Enum.map(~w(alloc vec Vec), &%{"Ident" => [&1, 0]})}
        }
      ]
    }

    {f, types}
  end

  test "Vec views reuse Aeneas borrowing and retain explicit generic filtering" do
    for method <- ~w(as_slice as_mut_slice) do
      {f, types} = example(method)
      mut = method == "as_mut_slice"

      assert %{
               1 => %{
                 builtin: false,
                 can_fail: false,
                 lift: ^mut,
                 keep_params: [true, false],
                 implementation_verified: false
               }
             } =
               CallModels.resolve([f], types, %{}, [])
    end
  end

  test "rejects altered view mutability, nominal type, lifetimes and unsafe signatures" do
    {f, types} = example("as_mut_slice")

    for bad <- [
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "output", "Ref", Access.at(2)], "Shared"),
          put_in(f, ["signature", "inputs"], []),
          put_in(f, ["generics", "outlives"], []),
          put_in(f, ["item_meta", "name", Access.at(3)], %{"Ident" => ["into_iter", 0]})
        ] do
      assert CallModels.resolve([bad], types, %{}, []) == %{}
    end

    wrong =
      put_in(types, ["type_decls", Access.at(0), "item_meta", "name"], [
        %{"Ident" => ["FakeVec", 0]}
      ])

    assert CallModels.resolve([f], wrong, %{}, []) == %{}
  end

  defp owned_example(method) do
    {f, types} = example("as_slice")
    [input] = f["signature"]["inputs"]
    vector = Enum.at(input["Ref"], 1)
    t = %{"TypeVar" => %{"Free" => 0}}

    args = fn values ->
      %{"regions" => [], "types" => values, "trait_refs" => [], "const_generics" => []}
    end

    unit = %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args.([])}}

    trait = %{
      "def_id" => 9,
      "item_meta" => %{"name" => Enum.map(~w(core marker Destruct), &%{"Ident" => [&1, 0]})},
      "generics" => params(1, [], []),
      "is_unsafe" => false,
      "consts" => [],
      "types" => [],
      "implied_clauses" => [],
      "methods" => [
        %{
          "params" => Map.put(params(1, [%{"index" => 0}], []), "types", []),
          "kind" => %{"TraitMethod" => [9, 0]},
          "skip_binder" => %{
            "name" => "drop_glue",
            "default" => nil,
            "signature" => %{
              "is_unsafe" => true,
              "abi" => "Rust",
              "is_variadic" => false,
              "inputs" => [%{"Ref" => [%{"Var" => %{"Bound" => [0, 0]}}, t, "Mut"]}],
              "output" => unit
            }
          }
        }
      ]
    }

    f = put_in(f, ["item_meta", "name", Access.at(3)], %{"Ident" => [method, 0]})

    f =
      case method do
        "new" ->
          f
          |> Map.put("generics", params(1, [], []))
          |> put_in(
            ["item_meta", "name", Access.at(2), "Impl", "Ty", "params"],
            params(1, [], [])
          )
          |> put_in(["signature", "inputs"], [])
          |> put_in(["signature", "output"], vector)

        "len" ->
          put_in(f, ["signature", "output"], %{
            "Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}
          })

        "push" ->
          clause = fn variable ->
            %{
              "clause_id" => 0,
              "trait_" => %{
                "regions" => [],
                "outlives" => [],
                "skip_binder" => %{"id" => 9, "generics" => args.([variable])}
              }
            }
          end

          f
          |> put_in(["generics", "trait_clauses"], [clause.(%{"TypeVar" => %{"Free" => 1}})])
          |> put_in(
            ["item_meta", "name", Access.at(2), "Impl", "Ty", "params", "trait_clauses"],
            [clause.(%{"TypeVar" => %{"Bound" => [1, 1]}})]
          )
          |> put_in(["signature", "inputs"], [put_in(input, ["Ref", Access.at(2)], "Mut"), t])
          |> put_in(["signature", "output"], unit)
      end

    {f, Map.put(types, "trait_decls", [trait])}
  end

  test "scalar vector construction length and push retain typed builtin identities" do
    for method <- ~w(new len push) do
      {f, types} = owned_example(method)
      fail = method == "push"

      assert %{1 => %{vec_owned_method: ^method, builtin: true, can_fail: ^fail}} =
               CallModels.resolve([f], types, %{}, [])

      for bad <- [
            put_in(f, ["signature", "abi"], "C"),
            put_in(f, ["signature", "inputs"], [%{}]),
            put_in(f, ["signature", "output"], %{}),
            put_in(f, ["generics", "const_generics"], [%{}])
          ] do
        assert CallModels.resolve([bad], types, %{}, []) == %{}
      end
    end
  end

  test "push validates the actual destructor trait and scalar Global instantiations" do
    {f, types} = owned_example("push")

    assert CallModels.resolve(
             [f],
             put_in(types, ["trait_decls", Access.at(0), "is_unsafe"], true),
             %{},
             []
           ) == %{}

    models = CallModels.resolve([f], types, %{}, [])
    scalar = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U16"}}}

    global = %{
      "Adt" => %{
        "id" => 6,
        "builtin" => nil,
        "generics" => %{
          "regions" => [],
          "types" => [],
          "const_generics" => [],
          "trait_refs" => []
        }
      }
    }

    global_decl = %{
      "def_id" => 6,
      "item_meta" => %{"name" => Enum.map(~w(alloc alloc Global), &%{"Ident" => [&1, 0]})},
      "generics" => Map.put(params(1, [], []), "types", [])
    }

    types = Map.update!(types, "type_decls", &(&1 ++ [global_decl]))

    caller = fn element, allocator ->
      %{
        "body" => %{
          "Regular" => %{
            "kind" => %{"Fun" => 1},
            "generics" => %{"types" => [element, allocator]}
          }
        },
        "item_meta" => %{"name" => []}
      }
    end

    assert :ok = Lynx.Rust.CollectionModels.audit([caller.(scalar, global)], models, types, %{})

    for {element, allocator} <- [
          {%{"Ref" => []}, global},
          {%{"TypeVar" => %{"Free" => 0}}, global},
          {scalar, %{}}
        ] do
      assert {:error, _, _} =
               Lynx.Rust.CollectionModels.audit([caller.(element, allocator)], models, types, %{})
    end

    assert {:error, _, _} =
             Lynx.Rust.CollectionModels.audit(
               [caller.(scalar, global)],
               models,
               put_in(types, ["type_decls", Access.at(-1), "item_meta", "name"], [
                 %{"Ident" => ["Other", 0]}
               ]),
               %{}
             )
  end

  @tag :tmp_dir
  test "bounded model assembly preserves literals and rejects application name collisions", %{
    tmp_dir: tmp
  } do
    path = Path.join(tmp, "Probe/Extraction/Funs.lean")
    File.mkdir_p!(Path.dirname(path))

    source =
      "module\npublic import Aeneas\n-- alloc.vec.Vec.push\ndef message := \"alloc.vec.Vec.push\"\ndef example := alloc.vec.Vec.push values value\n"

    File.write!(path, source)
    audit = %{external_calls: %{1 => %{vec_owned_method: "push"}}}

    assert ["Probe.Extraction.VectorModel"] =
             Lynx.Rust.CollectionModels.install!(
               audit,
               %{"functions" => []},
               tmp,
               "Probe.Extraction"
             )

    changed = File.read!(path)
    assert changed =~ "-- alloc.vec.Vec.push"
    assert changed =~ "def message := \"alloc.vec.Vec.push\""
    assert changed =~ "def example := _root_.Probe.Extraction.VectorModel.push values value"
    File.write!(path, source)

    assert_raise ArgumentError, ~r/ambiguous application Vec::push/, fn ->
      Lynx.Rust.CollectionModels.install!(
        audit,
        %{"functions" => [%{"lean_name" => "app.alloc.vec.Vec.push"}]},
        tmp,
        "Probe.Extraction"
      )
    end
  end
end
