defmodule Lynx.Rust.IoDefaultsSelectionTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.IoDefaults
  defp name(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp function(id, name, body),
    do: %{"def_id" => id, "item_meta" => %{"name" => name}, "body" => body}

  defp fixture(target) do
    %{
      "fun_decls" => [
        function(1, name(~w(protocol parse)), %{"Fun" => target}),
        function(2, name(~w(alloc io read Read read_exact)), %{"Fun" => 3}),
        function(3, name(~w(alloc io read default_read_exact)), %{"Global" => %{"id" => 9}}),
        function(4, name(~w(alloc io impls slice_read_exact)), %{"Global" => %{"id" => 9}}),
        function(5, name(~w(core error initializer)), %{})
      ],
      "global_decls" => [
        %{
          "def_id" => 9,
          "value" => %{"Value" => [10, [%{"Call" => [%{"kind" => %{"Fun" => 5}}, []]}, %{}]]}
        }
      ]
    }
  end

  test "retains called defaults and their transitive constant dependencies" do
    translated = fixture(2)
    needed = IoDefaults.needed_defaults(translated)
    assert MapSet.new([1, 2, 3, 4, 5]) == needed
    assert Enum.all?(translated["fun_decls"], &IoDefaults.retained?(&1, needed))
  end

  test "an overridden method does not require its unused default implementation" do
    translated = fixture(4)
    needed = IoDefaults.needed_defaults(translated)
    assert MapSet.new([1, 4, 5]) == needed
    [_, default, helper | _] = translated["fun_decls"]
    refute IoDefaults.retained?(default, needed)
    refute IoDefaults.retained?(helper, needed)
  end
end
