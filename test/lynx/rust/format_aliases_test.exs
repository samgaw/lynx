defmodule Lynx.Rust.FormatAliasesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.FormatModels

  defp fixture do
    foreign = %{
      "def_id" => 1,
      "body" => "Opaque",
      "signature" => %{"inputs" => [], "output" => "Unit"},
      "item_meta" => %{"name" => [%{"Ident" => ["foreign", 0]}], "is_local" => false}
    }

    local = %{
      "def_id" => 2,
      "body" => %{"Call" => 1},
      "item_meta" => %{"name" => [%{"Ident" => ["local", 0]}], "is_local" => true}
    }

    translated = %{"fun_decls" => [foreign, local], "type_decls" => [], "trait_decls" => []}
    model = %{bounded_formatting: true, function: foreign}

    audit = %{
      external_calls: %{1 => model},
      available_external_calls: %{1 => model},
      translated: translated,
      references: %{}
    }

    {%{"translated" => translated}, audit}
  end

  test "backend aliases preserve the actual first-party body, call IDs and foreign signature" do
    {document, audit} = fixture()

    {lowered, [{"fun_decls", 1, original, alias_name}]} =
      FormatModels.lower_names!(document, audit)

    assert [foreign, local] = document["translated"]["fun_decls"]
    assert [renamed, ^local] = lowered["translated"]["fun_decls"]
    assert foreign["item_meta"]["name"] == original
    assert put_in(renamed, ["item_meta", "name"], original) == foreign
    assert alias_name == [%{"Ident" => ["lynx_format", 0]}, %{"Ident" => ["function_1", 0]}]
  end

  test "stale, local or implemented declarations cannot acquire an opaque model alias" do
    {document, audit} = fixture()
    [foreign, local] = document["translated"]["fun_decls"]

    for altered <- [
          put_in(foreign, ["signature", "inputs"], ["changed"]),
          put_in(foreign, ["body"], %{"Return" => 0}),
          put_in(foreign, ["item_meta", "is_local"], true),
          put_in(foreign, ["item_meta", "name"], [%{"Ident" => ["another", 0]}])
        ] do
      changed = put_in(document, ["translated", "fun_decls"], [altered, local])

      assert_raise ArgumentError, ~r/original audited foreign declaration/, fn ->
        FormatModels.lower_names!(changed, audit)
      end
    end
  end

  test "existing declarations cannot be shadowed by backend aliases" do
    {document, audit} = fixture()

    collision = %{
      "def_id" => 3,
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["lynx_format", 0]},
          %{"Ident" => ["function_1", 0]}
        ]
      }
    }

    changed = update_in(document, ["translated", "fun_decls"], &(&1 ++ [collision]))
    assert_raise ArgumentError, ~r/collides/, fn -> FormatModels.lower_names!(changed, audit) end
  end

  @tag :tmp_dir
  test "unrelated extraction does not install or select formatting models", %{tmp_dir: tmp} do
    audit = %{external_calls: %{}, available_external_calls: %{}}
    assert FormatModels.scope(audit, "Example.Extraction") == audit
    assert FormatModels.type_models(%{}, "Example.Extraction") == []
    assert FormatModels.external_names(%{}) == %{}
    assert FormatModels.install!(%{}, tmp, "Example.Extraction") == []
    refute File.exists?(Path.join(tmp, "Example/NativeFormatting.lean"))
  end
end
