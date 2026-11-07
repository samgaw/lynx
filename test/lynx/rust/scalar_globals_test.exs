defmodule Lynx.Rust.ScalarGlobalsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{Constants, ScalarGlobals}

  defp parameters,
    do: %{
      "regions" => [],
      "types" => [],
      "const_generics" => [],
      "trait_clauses" => [],
      "outlives" => [],
      "trait_type_constraints" => []
    }

  defp arguments,
    do: %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  defp scalar(width),
    do: %{
      "Scalar" => %{
        "Integer" => %{
          if(String.starts_with?(width, "U"), do: "Unsigned", else: "Signed") => width
        }
      }
    }

  defp declaration(width, name) do
    parent = scalar(width)
    type = if name == "BITS", do: scalar("U32"), else: parent

    meta = %{
      "opacity" => "Opaque",
      "name" => [
        %{"Ident" => ["core", 0]},
        %{"Ident" => ["num", 0]},
        %{
          "Impl" => %{
            "Ty" => %{
              "kind" => "InherentImplBlock",
              "params" => parameters(),
              "skip_binder" => parent
            }
          }
        },
        %{"Ident" => [name, 0]}
      ]
    }

    global = %{
      "def_id" => 6,
      "src" => "Normal",
      "global_kind" => "NamedConst",
      "generics" => parameters(),
      "item_meta" => meta,
      "ty" => type,
      "value" => %{
        "Value" => [
          0,
          [%{"Call" => [%{"kind" => %{"Fun" => 45}, "generics" => arguments()}, []]}, type]
        ]
      }
    }

    initializer = %{
      "def_id" => 45,
      "src" => %{"GlobalInitializer" => %{"id" => 6, "generics" => arguments()}},
      "generics" => parameters(),
      "item_meta" => meta,
      "body" => "Opaque",
      "signature" => %{
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [],
        "output" => type
      }
    }

    {global, initializer}
  end

  test "uses existing Aeneas models for all fixed-width scalar bounds and bit widths" do
    for width <- ~w(U8 U16 U32 U64 U128 I8 I16 I32 I64 I128), name <- ~w(MIN MAX BITS) do
      {global, initializer} = declaration(width, name)
      expected = "Aeneas.Std.core.num.#{width}.#{name}"

      assert %{"lean_name" => ^expected, "implementation_verified" => false} =
               ScalarGlobals.resolve(global, [initializer], %{})

      models =
        ScalarGlobals.models(%{"global_decls" => [global], "fun_decls" => [initializer]}, %{})

      assert %{6 => %{"modelled" => true, "implementation_verified" => false} = model} =
               Constants.link!(models, %{"globals" => []})

      assert model["label"] =~ "not implementation verified"
      assert Constants.initializer_id(models[6]) == nil
    end
  end

  test "rejects wrong declaration identities, types and unsupported constants" do
    {global, initializer} = declaration("U16", "MAX")

    changes = [
      {["src"], "Other"},
      {["global_kind"], "AnonConst"},
      {["item_meta", "opacity"], "Transparent"},
      {["item_meta", "name", Access.at(0), "Ident", Access.at(0)], "application"},
      {["item_meta", "name", Access.at(3), "Ident", Access.at(0)], "OTHER"},
      {["generics", "outlives"], [%{}]},
      {["ty"], scalar("U32")},
      {["value", "Value", Access.at(1), Access.at(1)], scalar("U32")}
    ]

    for {path, value} <- changes,
        do: assert(is_nil(ScalarGlobals.resolve(put_in(global, path, value), [initializer], %{})))

    for width <- ~w(Usize Isize) do
      {g, i} = declaration(width, "MAX")
      assert is_nil(ScalarGlobals.resolve(g, [i], %{}))
    end

    assert is_nil(ScalarGlobals.resolve(global, [], %{}))
    assert is_nil(ScalarGlobals.resolve(global, [initializer, initializer], %{}))
  end

  test "requires the matching monomorphic safe Rust initializer" do
    {global, initializer} = declaration("U16", "MAX")

    for {path, value} <- [
          {["def_id"], 46},
          {["src", "GlobalInitializer", "id"], 7},
          {["generics", "outlives"], [%{}]},
          {["body"], %{"Structured" => %{}}},
          {["signature", "is_unsafe"], true},
          {["signature", "is_variadic"], true},
          {["signature", "abi"], "C"},
          {["item_meta", "opacity"], "Transparent"},
          {["signature", "inputs"], [scalar("U16")]},
          {["signature", "output"], scalar("U32")},
          {["item_meta", "name", Access.at(3), "Ident", Access.at(0)], "MIN"}
        ] do
      assert is_nil(ScalarGlobals.resolve(global, [put_in(initializer, path, value)], %{}))
    end
  end

  test "rejects duplicate scalar constant identities and competing generated definitions" do
    {global, initializer} = declaration("U16", "MAX")

    assert_raise ArgumentError, ~r/duplicate LLBC scalar constant identity/, fn ->
      ScalarGlobals.models(
        %{"global_decls" => [global, global], "fun_decls" => [initializer]},
        %{}
      )
    end

    models =
      ScalarGlobals.models(%{"global_decls" => [global], "fun_decls" => [initializer]}, %{})

    assert_raise ArgumentError, ~r/inconsistent Aeneas constant definition/, fn ->
      Constants.link!(models, %{"globals" => [%{"def_id" => 6, "lean_name" => "replacement"}]})
    end
  end
end
