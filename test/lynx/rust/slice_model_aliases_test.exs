defmodule Lynx.Rust.SliceModelAliasesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.SliceModels

  defp name(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp fixture do
    type = %{
      "def_id" => 3,
      "item_meta" => %{"name" => name(~w(core ops range RangeFrom))},
      "generics" => %{"types" => [%{"index" => 0}]},
      "kind" => %{"Struct" => [%{"name" => "start", "ty" => %{"TypeVar" => %{"Free" => 0}}}]}
    }

    method = fn id ->
      %{
        "def_id" => id,
        "body" => "Opaque",
        "src" => %{"TraitImpl" => %{"impl_ref" => %{"id" => 10}}}
      }
    end

    document = %{
      "translated" => %{
        "type_decls" => [type],
        "fun_decls" => [method.(1), method.(2)],
        "global_decls" => [],
        "ordered_decls" => [%{"Fun" => %{"NonRec" => 1}}, %{"Fun" => %{"NonRec" => 2}}]
      }
    }

    model = %{
      rust_name:
        "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::index",
      slice_range_from_checked: true,
      builtin: false,
      function: method.(1)
    }

    {document, %{1 => model}}
  end

  test "unused shared-index models do not change a different reader's dictionary" do
    {_, checked} = fixture()
    available = Map.put(checked, 3, %{builtin: true, lean: "packaged"})
    assert %{3 => %{builtin: true}} = SliceModels.backend_calls(available, %{})
    scoped = put_in(checked, [1, :lean], "Proofs.SliceModel.indexFrom")

    assert %{1 => %{lean: "Proofs.SliceModel.indexFrom"}, 3 => %{builtin: true}} =
             SliceModels.backend_calls(available, scoped)
  end

  test "keeps nominal identity and fields while selecting the checked dictionary" do
    {document, calls} = fixture()
    {backend, [alias], models} = SliceModels.lower_names!(document, calls)
    assert %{type_id: 3, omitted_unreferenced_functions: [2]} = alias
    [before] = document["translated"]["type_decls"]
    [after_type] = backend["translated"]["type_decls"]
    assert put_in(before, ["item_meta", "name"], alias.renamed) == after_type
    assert [_, nil] = backend["translated"]["fun_decls"]
    assert [%{"Fun" => %{"NonRec" => 1}}] = backend["translated"]["ordered_decls"]
    assert models[1].backend_rust_name =~ "lynx_slice::RangeFrom"
    assert models[1].rust_name == calls[1].rust_name

    assert %{
             "types" => [_],
             "trait_impls" => [%{"extract_name" => "Proofs.SliceModel.rangeFrom"}]
           } = SliceModels.external_names(calls, "Proofs")
  end

  test "never removes a dictionary member referenced by a body or constant" do
    {document, calls} = fixture()

    for changed <- [
          update_in(
            document,
            ["translated", "fun_decls"],
            &(&1 ++ [%{"def_id" => 8, "src" => "Normal", "body" => %{"Fun" => 2}}])
          ),
          put_in(document, ["translated", "global_decls"], [%{"value" => %{"Fun" => 2}}])
        ] do
      assert_raise ArgumentError, ~r/unmodelled slice dictionary member is called/, fn ->
        SliceModels.lower_names!(changed, calls)
      end
    end
  end

  test "rejects namespace collisions and leaves other models unchanged" do
    {document, calls} = fixture()
    assert {^document, [], %{}} = SliceModels.lower_names!(document, %{})
    collision = %{"def_id" => 9, "item_meta" => %{"name" => name(~w(lynx_slice RangeFrom))}}
    document = update_in(document, ["translated", "type_decls"], &(&1 ++ [collision]))
    assert_raise ArgumentError, ~r/collides/, fn -> SliceModels.lower_names!(document, calls) end
  end
end
