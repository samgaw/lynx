defmodule Lynx.Rust.RootSelectionTest do
  use ExUnit.Case
  alias Lynx.Rust.RootSelection

  test "invalid options fail while another process holds the preparation lock" do
    owner = self()

    holder =
      Task.async(fn ->
        Lynx.External.with_preparation_lock(fn ->
          send(owner, :preparation_locked)

          receive do
            :release -> :ok
          end
        end)
      end)

    try do
      assert_receive :preparation_locked, 5_000

      checking =
        Task.async(fn ->
          for options <- [
                [root_attribute: true],
                [item_roots: ["demo::_"]],
                [excluded_functions: ["demo::function"]],
                [unknown_option: true]
              ] do
            assert_raise ArgumentError, fn ->
              Lynx.Rust.verify!("/unused", "unused", options)
            end

            assert_raise ArgumentError, fn ->
              Lynx.Rustler.prepare!("/unused", "unused", options)
            end
          end
        end)

      try do
        Task.await(checking, 2_000)
      after
        Task.shutdown(checking, :brutal_kill)
      end
    after
      send(holder.pid, :release)
      Task.shutdown(holder, 2_000)
    end
  end

  test "metadata selectors reject invalid paths before invoking extraction", context do
    for key <- [:item_roots, :excluded_functions],
        items <- [true, "demo::_", ["demo"], ["demo::*"], ["demo::_\n"], [1]] do
      assert_raise ArgumentError, ~r/invalid Rust metadata/, fn ->
        Lynx.Rust.Extraction.describe!(
          context,
          "/unused",
          ["demo::function"],
          "/unused",
          "Demo",
          [
            {key, items}
          ]
        )
      end
    end
  end

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

  test "path selection cannot silently omit a requested local implementation" do
    root = "demo::_::wrapper::_::calculate"
    assert :ok = RootSelection.validate!(document([body()]), [root], nil, ["demo"])

    for functions <- [[], [Map.put(body(), "body", "Opaque")], [body(), body()]] do
      assert_raise ArgumentError, ~r/selected by path/, fn ->
        RootSelection.validate!(document(functions), [root], nil, ["demo"])
      end
    end
  end

  test "dependency roots are checked against their actual bodies in either selection mode" do
    dependency =
      put_in(
        body(),
        ["item_meta", "name"],
        Enum.map(~w(dependency calculate), &%{"Ident" => [&1, 0]})
      )

    for attribute <- [nil, "verify::root"] do
      assert :ok =
               RootSelection.validate!(
                 document([dependency]),
                 ["dependency::calculate"],
                 attribute,
                 ["demo"],
                 ["demo", "dependency"]
               )

      assert_raise ArgumentError, ~r/dependency::calculate selected by path/, fn ->
        RootSelection.validate!(
          document([body()]),
          ["dependency::calculate"],
          attribute,
          ["demo"],
          ["demo", "dependency"]
        )
      end
    end
  end

  test "external models and nonliteral trait selectors retain their existing resolution" do
    assert :ok =
             RootSelection.validate!(
               document([]),
               ["core::mem::drop", "{impl Trait for Demo}::method"],
               nil,
               ["demo"],
               ["demo"]
             )
  end
end
