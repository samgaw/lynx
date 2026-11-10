defmodule Lynx.Rust.AllocatedFormatTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.FormatModels

  setup do
    path = Path.expand("../../fixtures/rust_format_arguments/allocated_format.json", __DIR__)
    %{"function" => function, "translated" => translated} = path |> File.read!() |> JSON.decode!()
    %{function: function, translated: translated}
  end

  test "admits the actual allocated format identity and checked Arguments signature", ctx do
    assert %{
             rust_name: "alloc::fmt::format",
             bounded_formatting: true,
             can_fail: true,
             lift: false,
             builtin: false
           } = FormatModels.resolve(ctx.function, ctx.translated, %{})
  end

  test "rejects altered ABI, lifetime, nominal output and argument layout", ctx do
    for function <- [
          put_in(ctx.function, ["signature", "abi"], "C"),
          put_in(ctx.function, ["signature", "is_unsafe"], true),
          put_in(ctx.function, ["generics", "regions"], []),
          put_in(ctx.function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.function, ["body"], %{})
        ] do
      assert FormatModels.resolve(function, ctx.translated, %{}) == nil
    end

    types =
      Enum.map(ctx.translated["type_decls"], fn d ->
        if List.last(d["item_meta"]["name"]) == %{"Ident" => ["Arguments", 0]},
          do: %{d | "kind" => %{"Struct" => []}},
          else: d
      end)

    assert FormatModels.resolve(ctx.function, %{ctx.translated | "type_decls" => types}, %{}) ==
             nil
  end
end
