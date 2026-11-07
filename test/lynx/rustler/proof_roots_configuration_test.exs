defmodule Lynx.Rustler.ProofRootsConfigurationTest do
  use ExUnit.Case, async: true

  test "invalid proof roots fail before toolchain or workspace preparation" do
    for roots <- [false, "crate::function", [""], ["function"], [:function]] do
      assert_raise ArgumentError, ~r/proof_roots/, fn ->
        Lynx.Rustler.prepare!("/unused", "unused", proof_roots: roots)
      end
    end
  end
end
