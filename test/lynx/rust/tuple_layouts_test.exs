defmodule Lynx.Rust.TupleLayoutsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{DropModels, LLBC, TupleLayouts}
  @fixture Path.expand("../../fixtures/rustler/tuple_layout.json", __DIR__)
  @drop Path.expand("../../fixtures/rustler/scalar_tuple_drop.json", __DIR__)

  setup do
    probe = @fixture |> File.read!() |> JSON.decode!()
    [wrapper] = probe["translated"]["type_decls"]
    type = hd(wrapper["kind"]["Struct"])["ty"]
    %{probe: probe, type: type}
  end

  test "admits only compiler-bounded tuples for the exact selected targets", c do
    assert TupleLayouts.validate!(c.probe, c.probe, c.type) == 16

    evidence = %{
      queries: [%{type: c.type, bytes: 16}],
      targets: c.probe["translated"]["target_information"]
    }

    assert TupleLayouts.allowed?(c.type, evidence, evidence.targets)
    refute TupleLayouts.allowed?(c.type, nil, evidence.targets)

    refute TupleLayouts.allowed?(
             c.type,
             %{evidence | queries: [%{type: c.type, bytes: 4096}]},
             evidence.targets
           )

    refute TupleLayouts.allowed?(c.type, evidence, [])
    refute TupleLayouts.allowed?(%{"Scalar" => "Bool"}, evidence, evidence.targets)
  end

  test "rejects changed type, ABI, compiler and target evidence", c do
    [wrapper] = c.probe["translated"]["type_decls"]

    for changed <- [
          Map.put(c.probe, "has_errors", true),
          put_in(c.probe, ["translated", "type_decls"], [
            put_in(wrapper, ["item_meta", "is_local"], false)
          ]),
          Map.put(c.probe, "charon_version", "unknown"),
          put_in(c.probe, ["translated", "target_information"], []),
          put_in(c.probe, ["translated", "type_decls"], [put_in(wrapper, ["kind", "Struct"], [])]),
          put_in(c.probe, ["translated", "type_decls"], [
            put_in(wrapper, ["generics", "types"], [%{"index" => 0}])
          ]),
          put_in(c.probe, ["translated", "type_decls"], [
            put_in(wrapper, ["kind", "Struct"], [%{"ty" => %{"Scalar" => "Bool"}}])
          ]),
          put_in(c.probe, ["translated", "type_decls"], [
            put_in(wrapper, ["layout", Access.at(0), "value", "repr", "repr_algo"], "Rust")
          ]),
          put_in(c.probe, ["translated", "type_decls"], [
            put_in(
              wrapper,
              [
                "layout",
                Access.at(0),
                "value",
                "variant_layouts",
                Access.at(0),
                "field_offsets",
                Access.at(0),
                "chosen"
              ],
              8
            )
          ])
        ] do
      assert_raise ArgumentError, ~r/inconsistent compiler tuple layout evidence/, fn ->
        TupleLayouts.validate!(changed, c.probe, c.type)
      end
    end
  end

  test "scalar tuple vector cleanup is explicit and rejects borrowed fields" do
    doc = @drop |> File.read!() |> JSON.decode!()
    t = doc["translated"]
    functions = Enum.filter(t["fun_decls"], &(&1 && &1["item_meta"]["is_local"]))

    assert {:ok, %{erasures: entries}} =
             DropModels.audit(functions, [], t, LLBC.type_references!(t), ["tuple_drop"])

    entries = entries |> Map.values() |> Enum.flat_map(&Map.get(&1, :instances, [&1]))

    assert Enum.any?(
             entries,
             &(&1[:element_drop_basis] == :scalar_tuple and
                 &1.supported_drop_kinds == ~w(Precise Conditional))
           )

    changed = borrowed(t)

    assert {:error, _, message} =
             DropModels.audit(
               Enum.filter(changed["fun_decls"], &(&1 && &1["item_meta"]["is_local"])),
               [],
               changed,
               LLBC.type_references!(changed),
               ["tuple_drop"]
             )

    assert message =~ "conditional Vec drop requires" or message =~ "missing or ambiguous"
  end

  defp borrowed(%{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}),
    do: %{
      "Ref" => [
        %{"Var" => %{"Free" => 0}},
        %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}},
        "Mut"
      ]
    }

  defp borrowed(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, borrowed(v)} end)
  defp borrowed(list) when is_list(list), do: Enum.map(list, &borrowed/1)
  defp borrowed(value), do: value
end
