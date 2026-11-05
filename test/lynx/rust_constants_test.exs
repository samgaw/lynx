defmodule Lynx.Rust.ConstantsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.LLBC

  defp arguments,
    do: %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  defp parameters,
    do: %{
      "regions" => [],
      "types" => [],
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => []
    }

  defp scalar, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
  defp name(value), do: [%{"Ident" => ["first_party", 0]}, %{"Ident" => [value, 0]}]
  defp reference(id), do: %{"Global" => %{"id" => id, "generics" => arguments()}}

  defp input do
    meta = %{"name" => name("LIMIT"), "opacity" => "Transparent"}

    initializer = %{
      "def_id" => 11,
      "item_meta" => meta,
      "generics" => parameters(),
      "src" => %{"GlobalInitializer" => %{"id" => 10, "generics" => arguments()}},
      "signature" => %{
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [],
        "output" => scalar()
      },
      "body" => %{"Structured" => %{}}
    }

    caller = %{
      initializer
      | "def_id" => 0,
        "item_meta" => %{meta | "name" => name("read")},
        "src" => "Normal",
        "body" => %{"Structured" => reference(10)}
    }

    global = %{
      "def_id" => 10,
      "item_meta" => meta,
      "global_kind" => "NamedConst",
      "generics" => parameters(),
      "ty" => scalar(),
      "value" => %{
        "Value" => [
          50,
          [%{"Call" => [%{"kind" => %{"Fun" => 11}, "generics" => arguments()}, []]}, scalar()]
        ]
      }
    }

    %{
      "charon_version" => "0.1.304",
      "has_errors" => false,
      "translated" => %{
        "crate_name" => "first_party",
        "fun_decls" => [caller, initializer],
        "global_decls" => [global],
        "type_decls" => [],
        "files" => []
      }
    }
  end

  test "links immutable constants to actual initializer bodies separately from Rust functions" do
    audit = LLBC.audit!(input(), ["first_party"])
    assert [%{"def_id" => 0}] = audit.functions
    assert [%{"def_id" => 11}] = audit.constant_initializers
    assert %{0 => [11], 11 => []} = LLBC.dependencies(audit)

    translation = %{
      "charon_version" => "0.1.304",
      "aeneas_version" => "nightly-2026.11.04-2b9e3ea",
      "crate" => "first_party",
      "functions" => [%{"def_id" => 0, "lean_name" => "first_party.read", "is_opaque" => false}],
      "globals" => [
        %{
          "def_id" => 10,
          "lean_name" => "first_party.LIMIT",
          "lean_file" => "Native/Funs.lean",
          "can_fail" => true
        }
      ]
    }

    assert %{0 => %{}} = LLBC.link!(audit, translation)

    assert_raise ArgumentError, ~r/constant definition/, fn ->
      LLBC.link!(audit, %{translation | "globals" => []})
    end
  end

  test "rejects static, missing, mismatched and opaque constant definitions" do
    for document <- [
          put_in(input(), ["translated", "global_decls", Access.at(0), "global_kind"], %{
            "Static" => "Mut"
          }),
          put_in(input(), ["translated", "fun_decls"], [hd(input()["translated"]["fun_decls"])]),
          put_in(
            input(),
            ["translated", "fun_decls", Access.at(1), "src", "GlobalInitializer", "id"],
            12
          ),
          put_in(input(), ["translated", "fun_decls", Access.at(1), "signature", "output"], %{
            "Scalar" => "Bool"
          }),
          put_in(input(), ["translated", "fun_decls", Access.at(1), "body"], "Opaque")
        ] do
      error =
        try do
          LLBC.audit!(document, ["first_party"])
          nil
        rescue
          exception in [ArgumentError, CompileError] -> exception
        end

      assert error != nil
    end
  end

  test "promoted strings require the actual immutable builtin byte-slice type" do
    builtin = %{"Adt" => %{"id" => 20, "builtin" => "Str", "generics" => arguments()}}
    global = input()["translated"]["global_decls"] |> hd()

    global = %{
      global
      | "global_kind" => "AnonConst",
        "ty" => builtin,
        "value" => %{"Value" => [60, [%{"Str" => "configuration rejected"}, builtin]]}
    }

    declaration = %{
      "def_id" => 20,
      "item_meta" => %{"name" => [%{"Builtin" => ["Str", 0]}]},
      "generics" => parameters(),
      "kind" => %{
        "Struct" => [
          %{"ty" => %{"Slice" => [%{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}, nil]}}
        ]
      }
    }

    assert %{10 => _} = Lynx.Rust.Constants.audit!([global], [], %{}, [declaration])

    for invalid <- [
          put_in(declaration, ["item_meta", "name"], name("Str")),
          put_in(declaration, ["kind", "Struct", Access.at(0), "ty"], scalar())
        ] do
      assert_raise ArgumentError, ~r/inconsistent type/, fn ->
        Lynx.Rust.Constants.audit!([global], [], %{}, [invalid])
      end
    end
  end

  test "rejects missing references, global writes, mutable borrows and initializer cycles" do
    for operation <- [
          reference(99),
          %{"Assign" => [reference(10), %{}]},
          %{"Ref" => %{"kind" => "Mut", "place" => reference(10)}}
        ] do
      document =
        put_in(
          input(),
          ["translated", "fun_decls", Access.at(0), "body", "Structured"],
          operation
        )

      assert_raise CompileError, fn -> LLBC.audit!(document, ["first_party"]) end
    end

    cycle =
      put_in(
        input(),
        ["translated", "fun_decls", Access.at(1), "body", "Structured"],
        reference(10)
      )

    assert_raise CompileError, ~r/cyclic Rust constant/, fn ->
      LLBC.audit!(cycle, ["first_party"])
    end
  end
end
