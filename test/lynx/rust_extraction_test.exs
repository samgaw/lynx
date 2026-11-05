defmodule Lynx.Rust.ExtractionTest do
  use ExUnit.Case, async: true

  test "rejects target pointer widths or endian models that differ from the Lean runtime" do
    target = %{
      "translated" => %{
        "target_information" => [
          %{
            "key" => "host",
            "value" => %{
              "target_pointer_size" => :erlang.system_info(:wordsize),
              "is_little_endian" => true
            }
          }
        ]
      }
    }

    assert Lynx.Rust.Extraction.validate_target!(target) == :ok
    foreign_width = if :erlang.system_info(:wordsize) == 8, do: 4, else: 8

    for invalid <- [
          put_in(
            target,
            ["translated", "target_information", Access.at(0), "value", "target_pointer_size"],
            foreign_width
          ),
          put_in(
            target,
            ["translated", "target_information", Access.at(0), "value", "is_little_endian"],
            false
          ),
          put_in(target, ["translated", "target_information"], [])
        ] do
      assert_raise ArgumentError, ~r/unsupported Rust target for the Lean runtime/, fn ->
        Lynx.Rust.Extraction.validate_target!(invalid)
      end
    end
  end
end
