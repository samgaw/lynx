defmodule Lynx.Rustler.ScalarErrorDropsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC}
  alias Lynx.Rustler.{ErrorConstructors, ErrorDrops}
  @crates ~w(experiment_nif experiment_core experiment_analysis)
  @snapshot Path.expand("../../fixtures/rustler/scalar_error_drop.json", __DIR__)

  setup do
    JSON.decode!(File.read!(@snapshot))
    |> then(fn %{"document" => document, "layout" => layout} ->
      %{document: document, layout: layout}
    end)
  end

  test "drop-only internal roots request the compiled error layout", ctx do
    assert ErrorDrops.needed?(ctx.document, @crates)
    assert ErrorConstructors.needed?(ctx.document, @crates)
    refute ErrorDrops.needed?(ctx.document, ["unrelated"])
    {document, proof} = ErrorDrops.lower!(ctx.document, ctx.layout, @crates)
    assert [%{mode: {:scalar_result, "Bool"}}] = proof.sites
    assert [model] = Map.values(ErrorDrops.models!(document, proof))

    assert %{
             lean: "Lynx.Rustler.Decoding.dropScalarResultBool",
             implementation_verified: false,
             can_fail: true,
             function: %{"generics" => %{"types" => []}, "signature" => %{"inputs" => [input]}}
           } = model

    refs = LLBC.type_references!(document)
    assert %{"Adt" => %{"generics" => %{"types" => [scalar, _]}}} = CallModels.expand(input, refs)
    assert scalar == %{"Scalar" => "Bool"}
    assert model.label =~ "scalar Ok payloads"
    assert model.label =~ "boxed errors exhaust"
  end

  test "an unvalidated payload retains the partial generic cleanup", ctx do
    document = replace_bool(ctx.document)
    {document, proof} = ErrorDrops.lower!(document, ctx.layout, @crates)
    assert [%{mode: :result}] = proof.sites
    assert [model] = Map.values(ErrorDrops.models!(document, proof))
    assert model.lean == "Lynx.Rustler.Decoding.dropErrResult"
    assert model.label =~ "unknown Ok payloads exhaust"
  end

  # A TypeVar is deliberately not a validated primitive, even when callers
  # might instantiate it with Bool. No blanket Copy/no-drop assumption is made.
  defp replace_bool(%{"Scalar" => "Bool"}), do: %{"TypeVar" => %{"Free" => 0}}
  defp replace_bool(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, replace_bool(v)} end)
  defp replace_bool(list) when is_list(list), do: Enum.map(list, &replace_bool/1)
  defp replace_bool(value), do: value
end
