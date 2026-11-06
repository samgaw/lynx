defmodule Lynx.Rust.NativeBorrowsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeBorrows

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
