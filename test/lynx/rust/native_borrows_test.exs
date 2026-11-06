defmodule Lynx.Rust.NativeBorrowsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{NativeBorrows, NativeLifetimes}

  test "frame discovery terminates on recursive reference wrappers without native ownership" do
    args = %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}
    cycle = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args}}
    borrowed = %{"Ref" => ["Static", cycle, "Mut"]}

    type = %{
      "def_id" => 1,
      "src" => "Normal",
      "generics" => Map.merge(args, %{"trait_clauses" => []}),
      "item_meta" => %{
        "name" => [%{"Ident" => ["Cycle", 0]}],
        "attr_info" => %{"attributes" => []}
      },
      "kind" => %{"Struct" => [%{"ty" => borrowed}]}
    }

    function = %{
      "def_id" => 1,
      "item_meta" => %{"name" => [%{"Ident" => ["read_cycle", 0]}]},
      "signature" => %{"inputs" => [borrowed]},
      "body" => %{
        "Structured" => %{
          "locals" => %{"arg_count" => 1, "locals" => [%{"index" => 1, "ty" => borrowed}]},
          "body" => %{"statements" => [%{"kind" => "Return"}]}
        }
      }
    }

    NativeLifetimes.audit!(
      [function],
      %{},
      %{"type_decls" => [type], "fun_decls" => [function]},
      %{}
    )
  end

  test "classifies only closed primitive bitwise operators without erasing arithmetic failures" do
    for op <- ~w(BitAnd BitOr BitXor Add Sub Mul Div Rem Shl Shr) do
      function = %{
        "def_id" => 1,
        "body" => %{
          "Structured" => %{
            "body" => %{
              "statements" => [
                %{
                  "kind" => %{
                    "Assign" => [%{"kind" => %{"Local" => 0}}, %{"BinaryOp" => [op, %{}, %{}]}]
                  }
                },
                %{"kind" => "Return"}
              ]
            }
          }
        }
      }

      result = NativeBorrows.nonpanicking_calls([function], %{})
      assert MapSet.member?(result, 1) == op in ~w(BitAnd BitOr BitXor)
    end
  end
end
