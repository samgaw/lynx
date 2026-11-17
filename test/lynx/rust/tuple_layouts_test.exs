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

  test "compiler drop glue has no first-party crate path for tuple layout discovery", c do
    glue = %{
      "def_id" => 0,
      "item_meta" => %{
        "name" => [%{"Impl" => %{"Trait" => 6}}, %{"Builtin" => ["DropGlue", 0]}]
      }
    }

    document = put_in(c.probe, ["translated", "fun_decls"], [glue])
    assert %{queries: []} = TupleLayouts.prepare!(nil, nil, document, nil, nil, ["tuple_drop"])
  end

  test "vector arguments require unique matching layout and signed byte bounds", c do
    target = c.probe["translated"]["target_information"]

    translated = %{
      "target_information" => target,
      "type_decls" => [
        %{
          "def_id" => 1,
          "item_meta" => %{
            "name" => Enum.map(~w(alloc vec Vec), &%{"Ident" => [&1, 0]})
          }
        }
      ]
    }

    args = put_in(c.type, ["Adt", "generics", "types"], [c.type])["Adt"]["generics"]
    input = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args}}
    evidence = %{queries: [%{type: c.type, bytes: 16}], targets: target}
    refs = LLBC.type_references!(c.probe["translated"])

    assert [%{"bytes" => 16, "maximum" => 9_223_372_036_854_775_807}] =
             TupleLayouts.input_bounds!([input], translated, refs, evidence, 1_048_576)

    assert TupleLayouts.input_bounds!([], translated, refs, nil, 1_048_576) == []

    wide = %{evidence | queries: [%{type: c.type, bytes: 4096}]}

    assert [%{"bytes" => 4096, "maximum" => 9_223_372_036_854_775_807}] =
             TupleLayouts.input_bounds!([input], translated, refs, wide, 1_048_576)

    refute TupleLayouts.allowed?(c.type, wide, target)

    for missing <- [
          nil,
          %{evidence | queries: []},
          %{evidence | targets: []},
          %{evidence | queries: evidence.queries ++ evidence.queries}
        ] do
      assert_raise ArgumentError, ~r/tuple vector argument requires/, fn ->
        TupleLayouts.input_bounds!([input], translated, refs, missing, 1_048_576)
      end
    end

    narrow =
      put_in(translated, ["target_information", Access.at(0), "value", "target_pointer_size"], 4)

    for {bytes, accepted} <- [{2047, true}, {2048, false}] do
      evidence = %{
        evidence
        | queries: [%{type: c.type, bytes: bytes}],
          targets: narrow["target_information"]
      }

      if accepted do
        assert [%{"bytes" => ^bytes, "maximum" => 2_147_483_647}] =
                 TupleLayouts.input_bounds!([input], narrow, refs, evidence, 1_048_576)
      else
        assert_raise ArgumentError, ~r/native byte budget/, fn ->
          TupleLayouts.input_bounds!([input], narrow, refs, evidence, 1_048_576)
        end
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
