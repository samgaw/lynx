defmodule Lynx.Rustler.ErrorLiteralsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBCJson}
  alias Lynx.Rustler.ErrorLiterals
  @snapshot Path.expand("../../fixtures/rustler/error_literal.json", __DIR__)

  setup do
    data = @snapshot |> File.read!() |> JSON.decode!()
    context = Map.new(~w(document globals types), &{String.to_existing_atom(&1), data[&1]})
    context = Map.put(context, :refs, Map.new(data["refs"], fn [id, value] -> {id, value} end))
    %{context: context, operand: data["operand"], prefix: data["prefix"]}
  end

  test "resolves the actual compiled shared literal with a body-local lifetime", ctx do
    assert {:ok, "zero"} = read(ctx)
    refute ErrorLiterals.static_string?(ctx.operand["Move"]["ty"], ctx.context.refs)
    assert %{"Assign" => [_, %{"Ref" => _}]} = List.last(ctx.prefix)["kind"]
  end

  test "requires unique, immutable, well-typed compiled string provenance", ctx do
    [global] = ctx.context.globals

    for globals <- [
          [],
          [global, global],
          [put_in(global, ["item_meta", "opacity"], "Opaque")],
          [put_in(global, ["item_meta", "has_errors"], true)],
          [%{global | "global_kind" => "Static"}],
          [%{global | "ty" => %{"Scalar" => "Bool"}}],
          [%{global | "value" => %{"Value" => [23, [%{"Str" => "changed"}, global["ty"]]]}}]
        ] do
      assert :error = read(%{ctx | context: %{ctx.context | globals: globals}})
    end

    assert :error = read(%{ctx | context: %{ctx.context | types: []}})
    operand = update_in(ctx.operand, ["Move", "ty"], &poison_type(&1, ctx.context.refs))
    assert :error = read(%{ctx | operand: operand})

    load = List.last(ctx.prefix)

    bad_load =
      update_in(load, ["kind", "Assign", Access.at(0), "ty"], &poison_type(&1, ctx.context.refs))

    assert :error = read(%{ctx | prefix: [bad_load]})
  end

  test "validates the slice length independently from the type reference table", ctx do
    load = List.last(ctx.prefix)
    metadata = get_in(load, ["kind", "Assign", Access.at(1), "Ref", "ptr_metadata"])
    metadata = LLBCJson.restore_constant_references!(metadata, ctx.context.document)

    for length <- ["0", "3", "5", "-1"] do
      changed =
        put_in(
          metadata,
          ["Const", "Value", Access.at(1), Access.at(0), "Integer", "Unsigned", Access.at(1)],
          length
        )

      load = put_in(load, ["kind", "Assign", Access.at(1), "Ref", "ptr_metadata"], changed)

      assert :error =
               read(%{
                 ctx
                 | prefix: [load],
                   context: %{ctx.context | document: %{"metadata" => changed}}
               })
    end
  end

  test "does not recover an earlier literal across effects or overwritten locals", ctx do
    for kind <- [
          %{"Call" => %{}},
          %{"Drop" => %{}},
          %{"Switch" => %{}},
          %{"Assign" => [%{"kind" => %{"Projection" => []}}, %{"Use" => []}]},
          %{"StorageDead" => ctx.operand["Move"]["kind"]["Local"]},
          %{"Assign" => [ctx.operand["Move"], %{"Use" => [%{"Const" => %{}}, "Yes"]}]}
        ] do
      assert :error = read(%{ctx | prefix: ctx.prefix ++ [%{"kind" => kind}]})
    end

    assert :error = read(%{ctx | prefix: []})
  end

  test "follows same-block typed copies without admitting mutable references", ctx do
    source = ctx.operand["Move"]
    target = put_in(source, ["kind", "Local"], 100)
    copy = %{"kind" => %{"Assign" => [target, %{"Use" => [%{"Copy" => source}, "Yes"]}]}}

    assert {:ok, "zero"} =
             read(%{ctx | operand: %{"Copy" => target}, prefix: ctx.prefix ++ [copy]})

    %{"Ref" => [region, element, _]} = CallModels.expand(source["ty"], ctx.context.refs)
    mutable = put_in(source, ["ty"], %{"Ref" => [region, element, "Mut"]})
    assert :error = read(%{ctx | operand: %{"Move" => mutable}})
  end

  test "bounds literals to the common Rustler atom conversion subset", ctx do
    for text <- ["", String.duplicate("a", 255), <<0, 34, 92, 127>>] do
      assert {:ok, ^text} = read(with_literal(ctx, text))
    end

    for text <- [String.duplicate("a", 256), "λ", <<255>>] do
      assert :error = read(with_literal(ctx, text))
    end
  end

  defp read(ctx), do: ErrorLiterals.read(ctx.operand, ctx.prefix, ctx.context)

  defp poison_type(type, refs) do
    %{"Ref" => [region, %{"Adt" => adt}, shared]} = CallModels.expand(type, refs)
    %{"Ref" => [region, %{"Adt" => %{adt | "id" => 999}}, shared]}
  end

  defp with_literal(ctx, text) do
    [global] = ctx.context.globals
    load = List.last(ctx.prefix)
    global = put_in(global, ["value", "Value", Access.at(1), Access.at(0), "Str"], text)
    metadata = get_in(load, ["kind", "Assign", Access.at(1), "Ref", "ptr_metadata"])
    metadata = LLBCJson.restore_constant_references!(metadata, ctx.context.document)

    metadata =
      put_in(
        metadata,
        ["Const", "Value", Access.at(1), Access.at(0), "Integer", "Unsigned", Access.at(1)],
        Integer.to_string(byte_size(text))
      )

    load = put_in(load, ["kind", "Assign", Access.at(1), "Ref", "ptr_metadata"], metadata)

    %{
      ctx
      | context: %{ctx.context | globals: [global], document: %{"metadata" => metadata}},
        prefix: [load]
    }
  end
end
