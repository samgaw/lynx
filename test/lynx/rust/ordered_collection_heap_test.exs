defmodule Lynx.Rust.OrderedCollectionHeapTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{OrderedCollectionHeap, OrderedCollectionModels}

  @tag :tmp_dir
  test "runtime storage selects extensional contents while pure extraction stays unchanged", %{
    tmp_dir: tmp
  } do
    audit = %{ordered_collections: %{families: ["map"]}}
    assert [] = OrderedCollectionHeap.install!(audit, tmp, "Registry.Extraction", :pure)

    assert ["Registry.Extraction.OrderedCollectionsModel"] =
             OrderedCollectionModels.install!(audit, tmp, "Registry.Extraction", :runtime)

    path = Path.join(tmp, "Registry/Extraction/OrderedCollectionsModel.lean")
    assert File.read!(path) =~ "abbrev Map := Std.ExtTreeMap Nat U64"

    assert ["Registry.Extraction.OrderedCollectionHeap"] =
             OrderedCollectionHeap.install!(audit, tmp, "Registry.Extraction", :runtime)

    heap = Path.join(tmp, "Registry/Extraction/OrderedCollectionHeap.lean")
    original = File.read!(heap)
    assert original =~ "public import Registry.NativeRuntime"
    OrderedCollectionHeap.install!(audit, tmp, "Registry.Extraction", :runtime)
    assert File.read!(heap) == original
    OrderedCollectionModels.install!(audit, tmp, "Registry.Extraction", :pure)
    assert File.read!(path) =~ "abbrev Map := Std.TreeMap Nat U64"
  end

  @tag :tmp_dir
  test "refuses to replace a user-owned heap module", %{tmp_dir: tmp} do
    path = Path.join(tmp, "Registry/Extraction/OrderedCollectionHeap.lean")
    File.mkdir_p!(Path.dirname(path))
    source = "module\npublic def userProperty := True\n"
    File.write!(path, source)

    assert_raise ArgumentError, ~r/refusing to overwrite a user Lean module/, fn ->
      OrderedCollectionHeap.install!(
        %{ordered_collections: %{families: ["set"]}},
        tmp,
        "Registry.Extraction",
        :runtime
      )
    end

    assert File.read!(path) == source
  end
end
