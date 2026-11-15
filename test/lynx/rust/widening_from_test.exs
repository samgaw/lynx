defmodule Lynx.Rust.WideningFromTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.TryModels

  @snapshot JSON.decode!(
              File.read!(Path.expand("../../fixtures/rustler/widening_from.json", __DIR__))
            )

  test "reuses the upstream lossless conversion for each fixed-width widening" do
    for family <- ["Signed", "Unsigned"],
        lower <- [8, 16, 32],
        upper <- [16, 32, 64],
        lower < upper do
      prefix = if family == "Signed", do: "I", else: "U"
      {f, t} = conversion(family, prefix <> "#{lower}", family, prefix <> "#{upper}")

      assert %{lean: lean, builtin: true, can_fail: false, native_cutoff_only: true} =
               TryModels.resolve(f, t, %{})

      assert lean == "Aeneas.Std.core.convert.From#{prefix}#{upper}#{prefix}#{lower}.from"
    end
  end

  test "rejects narrowing, mixed-sign and malformed numeric trait implementations" do
    for {source_family, from, target_family, to} <- [
          {"Unsigned", "U64", "Unsigned", "U16"},
          {"Signed", "I16", "Unsigned", "U64"},
          {"Unsigned", "I16", "Unsigned", "I64"},
          {"Unsigned", "U16", "Unsigned", "U128"}
        ] do
      {f, t} = conversion(source_family, from, target_family, to)
      assert TryModels.resolve(f, t, %{}) == nil
    end

    f = @snapshot["function"]
    t = @snapshot["translated"]

    for changed <- [
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["src", "TraitImpl", "impl_ref", "generics", "types"], [%{}]),
          put_in(f, ["src", "TraitImpl", "trait_ref", "generics", "types"], []),
          put_in(f, ["generics", "outlives"], [%{}]),
          put_in(f, ["signature", "inputs"], []),
          put_in(f, ["item_meta", "name"], [])
        ],
        do: assert(TryModels.resolve(changed, t, %{}) == nil)
  end

  defp conversion(source_family, from, target_family, to) do
    map = fn value -> replace(value, source_family, from, target_family, to) end
    {map.(@snapshot["function"]), map.(@snapshot["translated"])}
  end

  defp replace(%{"Scalar" => %{"Integer" => %{"Unsigned" => "U16"}}}, family, from, _, _),
    do: %{"Scalar" => %{"Integer" => %{family => from}}}

  defp replace(%{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}, _, _, family, to),
    do: %{"Scalar" => %{"Integer" => %{family => to}}}

  defp replace(map, sf, f, tf, t) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, replace(v, sf, f, tf, t)} end)

  defp replace(list, sf, f, tf, t) when is_list(list),
    do: Enum.map(list, &replace(&1, sf, f, tf, t))

  defp replace(value, _, _, _, _), do: value
end
