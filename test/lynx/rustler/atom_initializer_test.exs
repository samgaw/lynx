defmodule Lynx.Rustler.AtomInitializerTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.AtomInitializer
  # Normal statement projection from the pinned Charon/Rustler 0.39 initializer.
  @snapshot JSON.decode!(
              File.read!(Path.expand("../../fixtures/rustler/atom_initializer.json", __DIR__))
            )

  defp fields!(snapshot) do
    AtomInitializer.fields!(
      snapshot["functions"],
      snapshot["type_id"],
      snapshot["fields"],
      Map.new(snapshot["literals"], fn {id, text} -> {String.to_integer(id), text} end),
      snapshot["constructors"],
      snapshot["expects"]
    )
  end

  test "recovers literal atoms in actual compiled aggregate field order" do
    assert fields!(@snapshot) == [
             %{"field" => "atom_ordered", "atom" => "ordered"},
             %{"field" => "atom_empty", "atom" => "empty"},
             %{"field" => "atom_equal", "atom" => "equal"}
           ]

    assert [%{"atom" => "changed"} | _] =
             fields!(put_in(@snapshot, ["literals", "16"], "changed"))
  end

  test "rejects missing, ambiguous and unsupported compiled initializers" do
    for changed <- [
          %{@snapshot | "functions" => []},
          %{@snapshot | "functions" => @snapshot["functions"] ++ @snapshot["functions"]},
          %{@snapshot | "constructors" => []},
          %{@snapshot | "expects" => []},
          %{@snapshot | "literals" => %{}},
          %{@snapshot | "fields" => []},
          %{@snapshot | "type_id" => 999},
          update_in(
            @snapshot,
            ["functions", Access.at(0), "body", "Structured", "body", "statements"],
            &[%{"kind" => %{"Switch" => %{}}} | &1]
          )
        ] do
      assert_raise ArgumentError, ~r/compiled Rustler atom initializer/, fn ->
        fields!(changed)
      end
    end
  end
end
