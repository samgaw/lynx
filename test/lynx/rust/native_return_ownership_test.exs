defmodule Lynx.Rust.NativeReturnOwnershipTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeLifetimes

  defp args(types),
    do: %{"types" => types, "regions" => [], "const_generics" => [], "trait_refs" => []}

  defp adt(id), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args([])}}
  defp place(id, type), do: %{"kind" => %{"Local" => id}, "ty" => type}

  defp fixture(destination, tail) do
    error = adt(1)
    result = adt(2)
    unit = %{"Adt" => %{"builtin" => "Tuple", "id" => 0, "generics" => args([])}}
    boolean = %{"Scalar" => "Bool"}

    locals =
      for {id, type} <- [{0, result}, {1, error}, {2, boolean}, {3, unit}, {4, result}],
          do: %{"index" => id, "ty" => type}

    moved = %{
      "kind" => %{
        "Assign" => [
          place(destination, result),
          %{
            "Aggregate" => [
              %{"Adt" => [%{"id" => 2, "builtin" => nil, "generics" => args([])}, 1, nil]},
              [%{"Move" => place(1, error)}]
            ]
          }
        ]
      }
    }

    consumed = %{
      "kind" => %{
        "Call" => %{
          "call" => %{
            "func" => %{"Regular" => %{"kind" => %{"Fun" => 10}}},
            "args" => [%{"Move" => place(1, error)}]
          },
          "dest" => place(3, unit)
        }
      }
    }

    empty_return = %{
      "kind" => %{
        "Assign" => [
          place(destination, result),
          %{
            "Aggregate" => [
              %{"Adt" => [%{"id" => 2, "builtin" => nil, "generics" => args([])}, 0, nil]},
              []
            ]
          }
        ]
      }
    }

    branch = %{
      "kind" => %{
        "Switch" => %{
          "data" => %{"scrutinee" => %{"Value" => %{"Copy" => place(2, boolean)}}},
          "branches" => [%{"statements" => [moved]}, %{"statements" => [consumed, empty_return]}]
        }
      }
    }

    function = %{
      "def_id" => 0,
      "item_meta" => %{"name" => [%{"Ident" => ["return_alternative", 0]}]},
      "signature" => %{"inputs" => [error, boolean], "output" => result},
      "body" => %{
        "Structured" => %{
          "locals" => %{"arg_count" => 2, "locals" => locals},
          "body" => %{"statements" => [branch | tail]}
        }
      }
    }

    parameters = Map.merge(args([]), %{"outlives" => [], "trait_type_constraints" => []})

    translated = %{
      "files" => [],
      "type_decls" => [
        %{
          "def_id" => 1,
          "src" => "Normal",
          "kind" => "Opaque",
          "generics" => Map.put(parameters, "trait_clauses", []),
          "item_meta" => %{"name" => Enum.map(~w(core io error Error), &%{"Ident" => [&1, 0]})}
        },
        %{
          "def_id" => 2,
          "kind" => %{
            "Enum" => [%{"id" => 0, "fields" => []}, %{"id" => 1, "fields" => [%{"ty" => error}]}]
          }
        }
      ],
      "fun_decls" => [function]
    }

    models = %{
      10 => %{
        native_io_error_drop: true,
        native_dispose: true,
        can_fail: true,
        native_cutoff_only: true
      }
    }

    {function, models, translated}
  end

  test "return alternatives retain conditional ownership without rejecting the return" do
    {function, models, translated} = fixture(0, [%{"kind" => "Return"}])
    NativeLifetimes.audit!([function], models, translated, %{})
  end

  test "a possibly owned return value still prevents an unmodeled panic" do
    panic = %{"kind" => %{"Panic" => %{"on_unwind" => %{"statements" => []}}}}
    {function, models, translated} = fixture(0, [panic])

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      NativeLifetimes.audit!([function], models, translated, %{})
    end
  end

  test "other local ownership cannot disappear across a branch join" do
    {function, models, translated} = fixture(4, [%{"kind" => "Return"}])

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      NativeLifetimes.audit!([function], models, translated, %{})
    end
  end
end
