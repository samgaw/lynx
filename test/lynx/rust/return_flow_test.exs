defmodule Lynx.Rust.ReturnFlowTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.ReturnFlow
  @args %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}
  @adt %{"id" => 4, "builtin" => nil, "generics" => @args}
  @types %{
    "type_decls" => [%{"def_id" => 4, "kind" => %{"Enum" => [%{"id" => 0}, %{"id" => 1}]}}]
  }

  test "an exhaustive returning enum match has no fallthrough" do
    assert ReturnFlow.returns?(
             [switch([block("Return"), block("Return")]), stmt("UndefinedBehavior")],
             @types,
             %{}
           )
  end

  test "partial matches and fallthrough branches cannot discard undefined behavior" do
    partial =
      put_in(switch([block("Return"), block("Return")]), ["kind", "Switch", "data", "branches"], [
        mapping(0, 0)
      ])

    for branch <- [partial, switch([block("Return"), block("Nop")])] do
      refute ReturnFlow.returns?([branch, stmt("UndefinedBehavior")], @types, %{})
    end
  end

  test "loop control remains unknown even with a later return" do
    for kind <- [%{"Break" => 0}, %{"Continue" => 0}, %{"Loop" => block("Return")}] do
      body = %{"statements" => [stmt(kind), stmt("Return")]}
      refute ReturnFlow.returns?([switch([body, block("Return")])], @types, %{})
    end
  end

  test "reachable undefined behavior and termination are never returning paths" do
    for kind <- ["UndefinedBehavior", "UnwindTerminate", "UnwindResume"] do
      refute ReturnFlow.returns?([stmt(kind), stmt("Return")], @types, %{})
      assert ReturnFlow.returns?([stmt("Return"), stmt(kind)], @types, %{})
    end
  end

  test "invalid branch indices or discriminant types do not establish completeness" do
    original = switch([block("Return"), block("Return")])

    wrong_type =
      put_in(
        original,
        ["kind", "Switch", "data", "scrutinee", "Discriminant", "ty", "Adt", "id"],
        9
      )

    bad_index =
      put_in(original, ["kind", "Switch", "data", "branches"], [mapping(0, 0), mapping(1, 8)])

    for invalid <- [wrong_type, bad_index],
        do: refute(ReturnFlow.returns?([invalid], @types, %{}))
  end

  test "an explicit valid fallback covers otherwise unmatched values" do
    original = switch([block("Return"), block("Return")])

    fallback =
      original
      |> put_in(["kind", "Switch", "data", "branches"], [mapping(0, 0)])
      |> put_in(["kind", "Switch", "data", "fallback"], 1)

    assert ReturnFlow.returns?([fallback], @types, %{})

    refute ReturnFlow.returns?(
             [put_in(fallback, ["kind", "Switch", "data", "fallback"], 8)],
             @types,
             %{}
           )
  end

  test "empty branch lists never establish a returning match" do
    refute ReturnFlow.returns?([switch([])], @types, %{})
  end

  test "fallthrough branches may continue to an explicit return" do
    assert ReturnFlow.returns?(
             [switch([block("Return"), block("Nop")]), stmt("Return")],
             @types,
             %{}
           )
  end

  test "duplicate variant identities cannot certify an exhaustive match" do
    types =
      put_in(@types, ["type_decls"], [
        %{"def_id" => 4, "kind" => %{"Enum" => [%{"id" => 0}, %{"id" => 0}]}}
      ])

    branch =
      put_in(switch([block("Return"), block("Return")]), ["kind", "Switch", "data", "branches"], [
        mapping(0, 0),
        mapping(0, 1)
      ])

    refute ReturnFlow.returns?([branch], types, %{})
  end

  defp stmt(kind), do: %{"kind" => kind}
  defp block(kind), do: %{"statements" => [stmt(kind)]}

  defp mapping(tag, index),
    do: [
      [%{"Discriminant" => [@adt, tag]}, %{"Scalar" => %{"Integer" => %{"Signed" => "Isize"}}}],
      index
    ]

  defp switch(branches),
    do:
      stmt(%{
        "Switch" => %{
          "data" => %{
            "scrutinee" => %{"Discriminant" => %{"ty" => %{"Adt" => @adt}}},
            "branches" => [mapping(0, 0), mapping(1, 1)],
            "fallback" => nil
          },
          "branches" => branches
        }
      })
end
