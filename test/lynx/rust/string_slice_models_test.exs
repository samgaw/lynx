defmodule Lynx.Rust.StringSliceModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, StringSliceModels}
  @snapshot Path.expand("../../fixtures/rustler/string_slices.json", __DIR__)

  test "resolves only shared standard string get implementations and retains dictionary dispatch" do
    t = snapshot()
    models = CallModels.resolve(t["fun_decls"], t, %{}, [])
    supported = for {_, m} <- models, m[:elaboration_only] != true, do: m
    assert Enum.sort(Enum.map(supported, & &1.string_slice_op)) == ~w(fromGet get rangeGet toGet)
    assert Enum.all?(supported, &(&1.status == :modelled and not &1.implementation_verified))

    for {_, m} <- models, kind = m[:str_range] do
      f = m.function
      trait = f["src"]["TraitImpl"]["trait_ref"]
      [range, str, _] = trait["generics"]["types"]

      dictionary = %{
        "regions" => [],
        "outlives" => [],
        "skip_binder" => %{
          "Value" => [
            0,
            %{
              "kind" => %{"TraitImpl" => f["src"]["TraitImpl"]["impl_ref"]},
              "trait_decl_ref" => trait
            }
          ]
        }
      }

      actual = %{
        "regions" => [%{"Erased" => nil}],
        "types" => [range, str],
        "const_generics" => [],
        "trait_refs" => [dictionary]
      }

      assert StringSliceModels.index_method!(actual, models, t, %{}, %{}) == f["def_id"]
      assert kind in ~w(Range RangeFrom RangeTo)

      for broken <- [Map.put(actual, "trait_refs", []), Map.put(actual, "types", [str, range])] do
        assert_raise ArgumentError, ~r/SliceIndex/, fn ->
          StringSliceModels.index_method!(broken, models, t, %{}, %{})
        end
      end

      assert_raise ArgumentError, ~r/SliceIndex/, fn ->
        StringSliceModels.index_method!(actual, Map.delete(models, f["def_id"]), t, %{}, %{})
      end
    end
  end

  test "rejects modified signatures, implementation identities and standard representations" do
    t = snapshot()

    for f <- t["fun_decls"],
        m = StringSliceModels.resolve(f, t, %{}),
        m && m[:elaboration_only] != true do
      for changed <- [
            Map.put(f, "body", %{"Structured" => %{}}),
            put_in(f, ["signature", "is_unsafe"], true),
            put_in(f, ["signature", "inputs"], []),
            put_in(f, ["signature", "output"], %{"Scalar" => "Bool"}),
            put_in(f, ["signature", "abi"], "C"),
            put_in(f, ["generics", "const_generics"], [%{}]),
            put_in(f, ["item_meta", "name"], [])
          ] do
        refute StringSliceModels.resolve(changed, t, %{})
      end
    end

    for type <- t["type_decls"], type && match?(%{"Struct" => _}, type["kind"]) do
      changed = put_in(type, ["kind", "Struct"], [])

      altered =
        Map.update!(
          t,
          "type_decls",
          &Enum.map(&1, fn row -> if row == type, do: changed, else: row end)
        )

      kind = List.last(type["item_meta"]["name"])["Ident"]

      affected =
        for f <- t["fun_decls"],
            m = StringSliceModels.resolve(f, t, %{}),
            m && m[:elaboration_only] != true && String.contains?(m.rust_name, "traits"),
            type["src"] == %{"Builtin" => "Str"} or kind == [m[:str_range], 0],
            do: f

      if affected != [] do
        assert Enum.all?(affected, &is_nil(StringSliceModels.resolve(&1, altered, %{})))
      end
    end
  end

  test "unused dictionary methods are exhaustion-only and cannot count as supported semantics" do
    t = snapshot()
    models = CallModels.resolve(t["fun_decls"], t, %{}, [])
    unused = for {_, m} <- models, m[:elaboration_only], do: m
    assert length(unused) == 15

    assert Enum.all?(
             unused,
             &(String.contains?(&1.label, "exhaustion") and not &1.implementation_verified)
           )
  end

  defp snapshot, do: JSON.decode!(File.read!(@snapshot))["translated"]
end
