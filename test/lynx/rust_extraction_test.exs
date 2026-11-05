defmodule Lynx.Rust.ExtractionTest do
  use ExUnit.Case, async: true

  @tag :tmp_dir
  test "retains extractor diagnostics when Charon emits incomplete LLBC with exit status zero", %{
    tmp_dir: tmp
  } do
    path = Path.join(tmp, "application.llbc")
    diagnostic = "error: unsupported constant at src/protocol.rs:42:7"
    File.write!(path, JSON.encode!(%{"has_errors" => true}))

    error =
      assert_raise ArgumentError, fn -> Lynx.Rust.Extraction.read_llbc!(path, diagnostic) end

    assert Exception.message(error) =~ path
    assert Exception.message(error) =~ diagnostic

    File.write!(path, JSON.encode!(%{"has_errors" => false}))
    assert %{"has_errors" => false} = Lynx.Rust.Extraction.read_llbc!(path, "")
  end

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
