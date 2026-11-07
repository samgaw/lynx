defmodule Lynx.Rust.NeverTypeTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC}

  test "rehydrates associated type metadata from its own type table" do
    associated = %{"TraitType" => ["Self", 0, %{"regions" => [], "types" => []}]}
    original = [%{"Value" => [73, associated]}, %{"Value" => [73, %{"data" => "span"}]}]
    removed = %{"ty" => %{"Deduplicated" => 73}}

    assert %{73 => ^associated} = LLBC.type_references!(original)

    assert %{"ty" => %{"Value" => [73, ^associated]}} =
             Lynx.Rust.LLBCJson.restore_type_references!(removed, original)
  end

  test "retains the uninhabited type without mixing independent hash-cons families" do
    document = [
      %{"Value" => [31, %{"Constant" => "unrelated"}]},
      %{"Value" => [31, "Never"]},
      %{"Value" => [31, %{"data" => %{"file_id" => 0}}]},
      %{"Value" => [31, %{"kind" => %{"Clause" => [%{"Free" => 0}, %{"regions" => []}]}}]}
    ]

    assert %{31 => "Never"} = references = LLBC.type_references!(document)
    assert CallModels.expand(%{"Deduplicated" => 31}, references) == "Never"

    assert %{"UnknownTypeReference" => 32} =
             CallModels.expand(%{"Deduplicated" => 32}, references)

    for conflicting <- [
          document ++ [%{"Value" => [31, %{"Scalar" => "Bool"}]}],
          [%{"Value" => [31, %{"Scalar" => "Bool"}]} | document]
        ] do
      assert_raise ArgumentError, ~r/inconsistent LLBC shared type identity/, fn ->
        LLBC.type_references!(conflicting)
      end
    end
  end
end
