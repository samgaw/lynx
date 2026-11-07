defmodule Lynx.Rust.LeanIdentifiersTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.LeanIdentifiers

  test "rewrites whole references while preserving generated literals and comments" do
    source = ~S"""
    let x ← alloc.vec.Vec.push values value
    let y ← Aeneas.Std.alloc.vec.Vec.push values value
    let z ← _root_.Aeneas.Std.alloc.vec.Vec.push values value
    let text := "alloc.vec.Vec.push and \"quoted\""
    let raw := r##"alloc.vec.Vec.push " inside"##
    let char := '"'
    let «alloc.vec.Vec.push» := 0
    -- alloc.vec.Vec.push
    /- outer alloc.vec.Vec.push /- nested alloc.vec.Vec.push -/ end -/
    other.alloc.vec.Vec.push values value
    alloc.vec.Vec.pushMore values value
    «λ»alloc.vec.Vec.push values value
    """

    names = [
      "_root_.Aeneas.Std.alloc.vec.Vec.push",
      "Aeneas.Std.alloc.vec.Vec.push",
      "alloc.vec.Vec.push"
    ]

    {rewritten, 4} = LeanIdentifiers.replace(source, names, "Models.push")
    assert rewritten =~ "let x ← Models.push"
    assert rewritten =~ "let y ← Models.push"
    assert rewritten =~ "let z ← Models.push"
    assert rewritten =~ ~S(let text := "alloc.vec.Vec.push and \"quoted\"")
    assert rewritten =~ ~S(r##"alloc.vec.Vec.push " inside"##)
    assert rewritten =~ "-- alloc.vec.Vec.push"
    assert rewritten =~ "/- nested alloc.vec.Vec.push -/"
    assert rewritten =~ "other.alloc.vec.Vec.push"
    assert rewritten =~ "alloc.vec.Vec.pushMore"
    assert rewritten =~ "«alloc.vec.Vec.push»"
  end

  test "does not match inside unicode names and rejects malformed generated tokens" do
    assert {"αalloc.vec.Vec.push", 0} =
             LeanIdentifiers.replace("αalloc.vec.Vec.push", ["alloc.vec.Vec.push"], "M.push")

    for prefix <- ["ά", "a＿", "a‍"] do
      source = prefix <> "alloc.vec.Vec.push"
      assert {^source, 0} = LeanIdentifiers.replace(source, ["alloc.vec.Vec.push"], "M.push")
    end

    for source <- [~S("unterminated), "«unterminated", "/- unterminated", ~S(r##"unterminated)] do
      assert_raise ArgumentError, fn ->
        LeanIdentifiers.replace(source, ["alloc.vec.Vec.push"], "M.push")
      end
    end
  end
end
