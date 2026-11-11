defmodule Lynx.Rustler.TaggedDecoderModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, IndexModels, LLBC, ResultModels, SliceModels}
  alias Lynx.Rustler.{AtomModels, DecoderModels}
  @snapshot Path.expand("../../fixtures/rustler/tagged_decoder_models.json", __DIR__)

  setup do
    doc = JSON.decode!(File.read!(@snapshot))
    t = doc["translated"]
    functions = Enum.reject(t["fun_decls"], &is_nil/1)
    refs = LLBC.type_references!(doc)
    models = CallModels.resolve(functions, t, refs, [:rustler_decoders])
    %{t: t, functions: functions, refs: refs, models: models}
  end

  test "Atom from_term reuses typed atom decoding with its SDK boundary", ctx do
    function = Enum.find(ctx.functions, &(leaf(&1) == "from_term"))

    assert %{lean: "Lynx.Rustler.Decoding.atom", can_fail: true, builtin: false} =
             DecoderModels.resolve(function, ctx.t, ctx.refs)

    for changed <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(function, ["generics", "regions"], [])
        ] do
      assert DecoderModels.resolve(changed, ctx.t, ctx.refs) == nil
    end
  end

  test "atom equality does not require an unreachable ne implementation", ctx do
    function = Enum.find(ctx.functions, &(leaf(&1) == "eq"))
    assert %{atom_eq: true} = AtomModels.resolve(function, ctx.t, ctx.refs)
    changed = put_in(function, ["signature", "is_unsafe"], true)
    assert AtomModels.resolve(changed, ctx.t, ctx.refs) == nil
  end

  test "safe slice get retains its actual indexing dictionary", ctx do
    functions = Enum.filter(ctx.functions, &(leaf(&1) == "get"))
    [wrapper] = Enum.filter(functions, &(IndexModels.resolve(&1, ctx.t, ctx.refs) != nil))

    assert %{lean: "Aeneas.Std.core.slice.Slice.get", builtin: true} =
             IndexModels.resolve(wrapper, ctx.t, ctx.refs)

    [index] = Enum.filter(functions, &(SliceModels.resolve(&1, ctx.t, ctx.refs) != nil))

    assert %{lean: "Aeneas.Std.core.slice.index.Usize.get"} =
             SliceModels.resolve(index, ctx.t, ctx.refs)

    for changed <- [
          put_in(wrapper, ["signature", "is_unsafe"], true),
          put_in(wrapper, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(wrapper, ["generics", "trait_clauses"], [])
        ],
        do: assert(IndexModels.resolve(changed, ctx.t, ctx.refs) == nil)
  end

  test "lifetime-bearing callbacks retain identity and reject generic captures", ctx do
    assert {:ok, deps} = ResultModels.audit(ctx.functions, ctx.models, ctx.t, ctx.refs)
    {_, callbacks} = Enum.find(deps, fn {_, ids} -> length(ids) == 3 end)
    assert length(callbacks) == 3
    callback = Enum.find(ctx.functions, &(&1["def_id"] == hd(callbacks)))
    assert callback["generics"]["regions"] != []

    closure =
      Enum.find(ctx.t["type_decls"], fn type ->
        case type do
          %{"src" => %{"Closure" => %{"info" => %{"closure_body" => %{"id" => id}}}}} ->
            id == callback["def_id"]

          _ ->
            false
        end
      end)

    changed =
      update_in(ctx.t, ["type_decls"], fn types ->
        Enum.map(types, fn type ->
          if type && type["def_id"] == closure["def_id"],
            do: put_in(type, ["kind", "Struct"], [%{"ty" => %{"TypeVar" => %{"Free" => 0}}}]),
            else: type
        end)
      end)

    assert {:error, _, message} = ResultModels.audit(ctx.functions, ctx.models, changed, ctx.refs)
    assert message =~ "extracted compiler FnOnce"
  end

  defp leaf(function), do: List.last(function["item_meta"]["name"])["Ident"] |> List.first()
end
