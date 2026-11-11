defmodule Lynx.Rust.StaticFormatTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.FormatModels
  @snapshot Path.expand("../../fixtures/rustler/static_format.json", __DIR__)

  setup do
    %{"function" => function, "translated" => translated} =
      JSON.decode!(File.read!(@snapshot))

    %{function: function, translated: translated}
  end

  test "binds the compiled static-text constructor to the existing format model", ctx do
    assert %{
             lean: "Aeneas.Std.core.fmt.Arguments.from_str",
             bounded_formatting: true,
             builtin: true
           } = FormatModels.resolve(ctx.function, ctx.translated, %{})
  end

  test "rejects altered static lifetime, mutability, output and ABI", ctx do
    [%{"Ref" => [_, text, _]}] = ctx.function["signature"]["inputs"]

    for function <- [
          put_in(ctx.function, ["signature", "inputs"], [
            %{"Ref" => [%{"Var" => %{"Free" => 0}}, text, "Shared"]}
          ]),
          put_in(ctx.function, ["signature", "inputs"], [%{"Ref" => ["Static", text, "Mut"]}]),
          put_in(ctx.function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.function, ["signature", "is_unsafe"], true),
          put_in(ctx.function, ["signature", "abi"], "C"),
          put_in(ctx.function, ["body"], %{"Structured" => %{}})
        ] do
      refute FormatModels.resolve(function, ctx.translated, %{})
    end
  end
end
