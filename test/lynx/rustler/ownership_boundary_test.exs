defmodule Lynx.Rustler.OwnershipBoundaryTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.Bindings

  test "custom values cannot silently lose their wrapper-side destructor" do
    for type <- [
          %{"native" => "Owned", "lean" => "Owned", "encoder" => "Owned.encode"},
          %{"resource" => "Owned", "lean" => "Owned"},
          %{"nif_result" => "bool"},
          %{"vec" => "u8"},
          "binary",
          %{"tuple" => ["bool", %{"native" => "Owned"}]},
          %{"tuple" => [], "native" => "Owned", "lean" => "Owned", "encoder" => "Owned.encode"}
        ] do
      manifest = %{
        bindings: [%{"name" => "owned", "arity" => 1, "arguments" => ["u64"], "result" => type}]
      }

      assert_raise ArgumentError, ~r/destructor-free value codecs.*owned\/1/, fn ->
        Bindings.validate_ownership!(manifest, :explicit)
      end

      assert :ok = Bindings.validate_ownership!(manifest, false)
    end
  end
end
