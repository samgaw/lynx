defmodule Lynx.Rust.MirTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.Mir

  test "selects compiler MIR stages without changing existing owned-drop defaults" do
    assert Mir.arguments!([]) == []

    for stage <- [:promoted, :elaborated, :optimized],
        do: assert(Mir.arguments!(mir: stage) == ["--mir", Atom.to_string(stage)])

    assert Mir.arguments!(owned_drops: true, execution: :runtime) == ["--mir", "optimized"]
    assert Mir.arguments!(owned_drops: true, execution: :runtime, futures: :cancelling) == []
  end

  test "rejects unsupported or conflicting stage choices before native preparation" do
    for options <- [
          [mir: "elaborated"],
          [mir: :built],
          [mir: true],
          [mir: :elaborated, execution: :runtime],
          [mir: :optimized, owned_drops: true]
        ] do
      assert_raise ArgumentError, ~r/mir/, fn -> Mir.validate!(options) end

      assert_raise ArgumentError, ~r/mir/, fn ->
        Lynx.Rust.verify!("/unused", "unused", options)
      end

      assert_raise ArgumentError, ~r/mir/, fn ->
        Lynx.Rustler.prepare!("/unused", "unused", options)
      end
    end
  end
end
