defmodule Lynx.Rust.NativeOwnedDropsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeOwnedDrops

  @tag :tmp_dir
  test "requires an exact compiler capability and runtime execution", %{tmp_dir: tmp} do
    for manifest <- [
          "charon=base\n",
          "charon=base+owned-drops-v10\n",
          "aeneas=base+owned-drops-v1\n"
        ] do
      File.write!(Path.join(tmp, "lynx-toolchain"), manifest)

      assert_raise ArgumentError, ~r/owned-drops-v1/, fn ->
        NativeOwnedDrops.arguments!(true, tmp)
      end
    end

    File.write!(Path.join(tmp, "lynx-toolchain"), "charon=base+owned-drops-v1\n")
    assert NativeOwnedDrops.arguments!(true, tmp) == ["--owned-drops"]
    assert NativeOwnedDrops.arguments!(false, "/unused") == []

    assert_raise ArgumentError, ~r/invalid owned_drops/, fn ->
      NativeOwnedDrops.arguments!(:all, tmp)
    end

    assert_raise ArgumentError, ~r/requires runtime execution/, fn ->
      apply(Lynx.Rust.Extraction, :run!, [
        %{},
        "/unused",
        ["probe::make"],
        "/unused",
        "Probe.Extraction",
        [owned_drops: true]
      ])
    end
  end
end
