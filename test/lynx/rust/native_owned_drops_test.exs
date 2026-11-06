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

  test "requires the actual emitted owning destructor before installing its dictionary" do
    plan = [%{"def_id" => 4, native_cleanup: 7}]

    function = %{
      "def_id" => 7,
      "rust_name" => "probe::Payload::drop_owned",
      "lean_name" => "probe.Payload.drop_owned",
      "is_opaque" => false,
      "is_rec" => false
    }

    translation = %{
      "functions" => [function],
      "types" => [%{"def_id" => 4, "lean_name" => "probe.Payload"}]
    }

    source = """
    namespace probe
    /-- [probe::Payload::drop_owned]: compiler body -/
    def Payload.drop_owned (payload : Payload) := NativeOwnedDrop.drop payload.mutex
    end probe
    """

    installed = NativeOwnedDrops.install_instances!(plan, translation, source)
    assert String.contains?(installed, "cleanup := probe.Payload.drop_owned")
    assert String.contains?(installed, "NativeOwnedDrop.drop payload.mutex")

    for invalid <- [source <> source, "namespace probe\nend probe\n"] do
      assert_raise ArgumentError, ~r/missing or ambiguous emitted/, fn ->
        NativeOwnedDrops.install_instances!(plan, translation, invalid)
      end
    end

    for invalid <- [put_in(translation, ["functions"], []), put_in(translation, ["types"], [])] do
      assert_raise ArgumentError, ~r/cleanup correspondence/, fn ->
        NativeOwnedDrops.install_instances!(plan, invalid, source)
      end
    end

    for key <- ~w(is_opaque is_rec) do
      invalid = put_in(translation, ["functions"], [Map.put(function, key, true)])

      assert_raise ArgumentError, ~r/unsupported owning destructor/, fn ->
        NativeOwnedDrops.install_instances!(plan, invalid, source)
      end
    end
  end
end
