defmodule Lynx.Rust.RootSelectionTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.RootSelection

  test "attributes are literal qualified Rust paths and invalid values fail before building" do
    assert RootSelection.attribute!(nil) == nil
    assert RootSelection.attribute!("verify::start_from") == "verify::start_from"

    for value <- [true, [], 12, "", "verify", "verify::", "verify::root\n", "verify::root;other"] do
      assert_raise ArgumentError, ~r/root_attribute/, fn -> RootSelection.attribute!(value) end

      assert_raise ArgumentError, ~r/root_attribute/, fn ->
        Lynx.Rustler.prepare!("/unused", "unused", root_attribute: value)
      end

      assert_raise ArgumentError, ~r/root_attribute/, fn ->
        Lynx.Rust.verify!("/unused", "unused", roots: ["demo::function"], root_attribute: value)
      end
    end
  end

  test "attribute selection bypasses local paths but retains dependency and trait roots" do
    roots = [
      "demo::_::wrapper::_::calculate",
      "core::mem::drop",
      "dependency::function",
      "{impl Trait for Demo}::method"
    ]

    assert RootSelection.arguments(roots, nil, ["demo"]) ==
             Enum.flat_map(roots, &["--start-from", &1])

    assert RootSelection.arguments(roots, "verify::root", ["demo"]) == [
             "--start-from-attribute=verify::root",
             "--start-from",
             "core::mem::drop",
             "--start-from",
             "dependency::function",
             "--start-from",
             "{impl Trait for Demo}::method"
           ]
  end

  defp body do
    %{
      "def_id" => 7,
      "body" => %{"return" => true},
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["demo", 0]},
          %{"Ident" => ["_", 3]},
          %{"Ident" => ["wrapper", 0]},
          %{"Builtin" => ["Closure", 0]},
          %{"Ident" => ["calculate", 0]}
        ]
      }
    }
  end

  defp document(functions),
    do: %{"translated" => %{"crate_name" => "demo", "fun_decls" => functions}}

  test "a requested nested body must actually be present, not just another selected function" do
    root = "demo::_::wrapper::_::calculate"

    assert RootSelection.validate!(document([nil, body()]), [root], "verify::root", ["demo"]) ==
             :ok

    assert RootSelection.validate!(
             document([body()]),
             ["crate::_::wrapper::_::calculate"],
             "verify::root",
             ["demo"]
           ) == :ok

    for functions <- [
          [],
          [Map.put(body(), "body", "Opaque")],
          [body(), body()],
          [put_in(body(), ["item_meta", "name"], [%{"Ident" => ["another", 0]}])]
        ] do
      assert_raise ArgumentError, ~r/missing, ambiguous or opaque Rust root/, fn ->
        RootSelection.validate!(document(functions), [root], "verify::root", ["demo"])
      end
    end
  end
end
