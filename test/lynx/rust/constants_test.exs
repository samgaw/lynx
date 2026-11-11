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

  defp promoted(type) do
    document = input()
    promoted_name = name("read") ++ [%{"Builtin" => ["PromotedConst", 0]}]
    [global] = document["translated"]["global_decls"]
    [caller, initializer] = document["translated"]["fun_decls"]
    meta = %{global["item_meta"] | "name" => promoted_name}

    global =
      %{global | "global_kind" => "AnonConst", "item_meta" => meta, "ty" => type}
      |> put_in(["value", "Value", Access.at(1), Access.at(1)], type)

    initializer =
      %{initializer | "item_meta" => meta}
      |> put_in(["signature", "output"], type)

    document
    |> put_in(["translated", "global_decls"], [global])
    |> put_in(["translated", "fun_decls"], [caller, initializer])
  end

  defp scalar_array(element, length) do
    usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
    %{"Array" => [element, [%{"Integer" => %{"Unsigned" => ["Usize", length]}}, usize], nil]}
  end

  test "promoted shared scalar arrays retain checked initializer identities" do
    for element <- [scalar(), %{"Scalar" => "Bool"}], size <- ["0", "4"] do
      type = %{"Ref" => ["Erased", scalar_array(element, size), "Shared"]}
      audit = LLBC.audit!(promoted(type), ["first_party"])
      assert %{0 => [11], 11 => []} = LLBC.dependencies(audit)

      assert %{10 => %{"inlined" => true, "initializer_id" => 11}} =
               Lynx.Rust.Constants.link!(audit.constants, %{"globals" => []})
    end
  end

  test "array lengths use constant identities independently of overlapping type IDs" do
    usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}

    type = %{
      "Ref" => [
        "Erased",
        %{"Value" => [81, %{"Array" => [scalar(), %{"Deduplicated" => 77}, nil]}]},
        "Shared"
      ]
    }

    document = promoted(type)

    document =
      update_in(
        document,
        ["translated", "fun_decls", Access.at(0), "body", "Structured"],
        fn body ->
          Map.merge(body, %{
            "type_table_entry" => %{"Value" => [77, scalar()]},
            "array_size" => %{
              "Value" => [77, [%{"Integer" => %{"Unsigned" => ["Usize", "4"]}}, usize]]
            }
          })
        end
      )

    audit = LLBC.audit!(document, ["first_party"])
    assert %{0 => [11], 11 => []} = LLBC.dependencies(audit)
    assert %{10 => _} = audit.constants

    missing =
      update_in(
        document,
        ["translated", "fun_decls", Access.at(0), "body", "Structured"],
        &Map.delete(&1, "array_size")
      )

    assert_raise ArgumentError, ~r/constant/, fn -> LLBC.audit!(missing, ["first_party"]) end
  end

  test "promoted arrays reject missing, opaque and mismatched initializer bodies" do
    type = %{"Ref" => ["Erased", scalar_array(scalar(), "4"), "Shared"]}
    document = promoted(type)
    wrong_type = %{"Ref" => ["Erased", scalar_array(scalar(), "5"), "Shared"]}

    for bad <- [
          put_in(document, ["translated", "fun_decls"], [hd(document["translated"]["fun_decls"])]),
          put_in(
            document,
            ["translated", "fun_decls", Access.at(1), "signature", "output"],
            wrong_type
          ),
          put_in(document, ["translated", "fun_decls", Access.at(1), "body"], "Opaque")
        ] do
      error =
        try do
          LLBC.audit!(bad, ["first_party"])
          nil
        rescue
          exception in [ArgumentError, CompileError] -> exception
        end

      assert error != nil
    end
  end

  test "promoted arrays reject unresolved lengths, non-scalar elements and mutable borrows" do
    for array <- [
          scalar_array(%{"Adt" => %{"id" => 0}}, "1"),
          scalar_array(scalar(), "-1"),
          scalar_array(scalar(), "04"),
          scalar_array(scalar(), "1tail"),
          scalar_array(scalar(), ""),
          %{"Array" => [scalar(), %{"Var" => %{"Free" => 0}}, nil]},
          %{"Array" => [scalar(), [%{"Integer" => %{"Signed" => ["Isize", "4"]}}, scalar()], nil]}
        ] do
      assert_raise ArgumentError, ~r/constant initializer/, fn ->
        LLBC.audit!(promoted(%{"Ref" => ["Erased", array, "Shared"]}), ["first_party"])
      end
    end

    assert_raise ArgumentError, ~r/constant initializer/, fn ->
      LLBC.audit!(promoted(%{"Ref" => ["Erased", scalar_array(scalar(), "4"), "Mut"]}), [
        "first_party"
      ])
    end
  end

  defp named_array(type) do
    input()
    |> put_in(["translated", "global_decls", Access.at(0), "ty"], type)
    |> put_in(
      ["translated", "global_decls", Access.at(0), "value", "Value", Access.at(1), Access.at(1)],
      type
    )
    |> put_in(["translated", "fun_decls", Access.at(1), "signature", "output"], type)
  end

  test "named scalar arrays retain actual initializer and Lean definition identities" do
    for element <- [scalar(), %{"Scalar" => "Bool"}], size <- ["0", "4"] do
      type = scalar_array(element, size)
      audit = LLBC.audit!(named_array(type), ["first_party"])
      assert %{0 => [11], 11 => []} = LLBC.dependencies(audit)
      assert %{10 => %{"global_kind" => "NamedConst", "ty" => ^type}} = audit.constants

      assert %{10 => %{"lean_name" => "first_party.LIMIT", "declaration" => _}} =
               Lynx.Rust.Constants.link!(audit.constants, %{
                 "globals" => [
                   %{
                     "def_id" => 10,
                     "lean_name" => "first_party.LIMIT",
                     "lean_file" => "Native/Funs.lean",
                     "can_fail" => false
                   }
                 ]
               })

      assert_raise ArgumentError, ~r/constant definition/, fn ->
        Lynx.Rust.Constants.link!(audit.constants, %{"globals" => []})
      end
    end
  end

  test "named arrays reject unsupported payloads, references and generic lengths" do
    for type <- [
          scalar_array(%{"Adt" => %{"id" => 0}}, "1"),
          scalar_array(scalar_array(scalar(), "2"), "1"),
          %{"Ref" => ["Erased", scalar_array(scalar(), "4"), "Shared"]},
          %{"Array" => [scalar(), %{"Var" => %{"Free" => 0}}, nil]}
        ] do
      assert_raise ArgumentError, ~r/constant initializer/, fn ->
        LLBC.audit!(named_array(type), ["first_party"])
      end
    end
  end

  test "named arrays reject mismatched and incomplete initializer implementations" do
    document = named_array(scalar_array(scalar(), "4"))

    for bad <- [
          put_in(
            document,
            ["translated", "fun_decls", Access.at(1), "signature", "output"],
            scalar_array(scalar(), "5")
          ),
          put_in(
            document,
            ["translated", "fun_decls", Access.at(1), "item_meta", "name"],
            name("OTHER")
          ),
          put_in(document, ["translated", "fun_decls", Access.at(1), "body"], "Opaque")
        ] do
      error =
        try do
          LLBC.audit!(bad, ["first_party"])
          nil
        rescue
          exception in [ArgumentError, CompileError] -> exception
        end

      assert error != nil
    end
  end

  test "promoted shared scalar borrows retain initializer dependencies through Aeneas inlining" do
    audit = LLBC.audit!(promoted(%{"Ref" => ["Erased", scalar(), "Shared"]}), ["first_party"])
    assert %{0 => [11], 11 => []} = LLBC.dependencies(audit)

    assert %{
             10 => %{
               "inlined" => true,
               "initializer_id" => 11,
               "rust_name" => "first_party::read::{promoted const#0}"
             }
           } = Lynx.Rust.Constants.link!(audit.constants, %{"globals" => []})

    assert %{10 => %{"lean_name" => "first_party.read.promoted"}} =
             Lynx.Rust.Constants.link!(audit.constants, %{
               "globals" => [
                 %{
                   "def_id" => 10,
                   "lean_name" => "first_party.read.promoted",
                   "lean_file" => "Native/Funs.lean",
                   "can_fail" => true
                 }
               ]
             })
  end

  defp lifetime_promotion do
    document = promoted(%{"Ref" => ["Erased", scalar(), "Shared"]})
    params = %{parameters() | "regions" => [%{"index" => 0}]}
    args = %{arguments() | "regions" => [%{"Var" => %{"Free" => 0}}]}

    document
    |> put_in(["translated", "global_decls", Access.at(0), "generics"], params)
    |> put_in(
      [
        "translated",
        "global_decls",
        Access.at(0),
        "value",
        "Value",
        Access.at(1),
        Access.at(0),
        "Call",
        Access.at(0),
        "generics"
      ],
      args
    )
    |> put_in(["translated", "fun_decls", Access.at(0), "generics"], params)
    |> put_in(
      ["translated", "fun_decls", Access.at(0), "body", "Structured", "Global", "generics"],
      args
    )
    |> put_in(["translated", "fun_decls", Access.at(1), "generics"], params)
    |> put_in(
      ["translated", "fun_decls", Access.at(1), "src", "GlobalInitializer", "generics"],
      args
    )
  end

  test "lifetime-only scalar promotions retain actual initializer dependencies" do
    audit = LLBC.audit!(lifetime_promotion(), ["first_party"])
    assert %{0 => [11], 11 => []} = LLBC.dependencies(audit)
    assert [%{"generics" => %{"regions" => [%{"index" => 0}]}}] = audit.constant_initializers
  end

  test "promoted scalar uses admit only bound body-local lifetime arguments" do
    for index <- [0, 2] do
      document =
        lifetime_promotion()
        |> put_in(
          ["translated", "fun_decls", Access.at(0), "body", "Structured", "bound_body_regions"],
          3
        )
        |> put_in(
          [
            "translated",
            "fun_decls",
            Access.at(0),
            "body",
            "Structured",
            "Global",
            "generics",
            "regions"
          ],
          [%{"Body" => index}]
        )

      audit = LLBC.audit!(document, ["first_party"])
      assert %{0 => [11], 11 => []} = LLBC.dependencies(audit)
    end

    for {bound, region} <- [
          {3, %{"Body" => -1}},
          {3, %{"Body" => 3}},
          {3, %{"Body" => "0"}},
          {nil, %{"Body" => 0}},
          {-1, %{"Body" => 0}},
          {"3", %{"Body" => 0}},
          {3, %{"Var" => %{"Bound" => [0, 0]}}}
        ] do
      document =
        lifetime_promotion()
        |> put_in(
          ["translated", "fun_decls", Access.at(0), "body", "Structured", "bound_body_regions"],
          bound
        )
        |> put_in(
          [
            "translated",
            "fun_decls",
            Access.at(0),
            "body",
            "Structured",
            "Global",
            "generics",
            "regions"
          ],
          [region]
        )

      assert_raise CompileError, ~r/constant reference/, fn ->
        LLBC.audit!(document, ["first_party"])
      end
    end
  end

  test "lifetime promotions reject mismatched binders and call-site regions" do
    for document <- [
          put_in(
            lifetime_promotion(),
            ["translated", "fun_decls", Access.at(1), "generics"],
            parameters()
          ),
          put_in(
            lifetime_promotion(),
            ["translated", "fun_decls", Access.at(0), "body", "Structured", "Global", "generics"],
            arguments()
          ),
          put_in(
            lifetime_promotion(),
            [
              "translated",
              "fun_decls",
              Access.at(0),
              "body",
              "Structured",
              "Global",
              "generics",
              "regions"
            ],
            [%{"Var" => %{"Free" => 1}}]
          ),
          put_in(
            lifetime_promotion(),
            ["translated", "global_decls", Access.at(0), "generics", "outlives"],
            [%{"skip_binder" => []}]
          )
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

  test "promoted scalar borrows reject mutation, non-scalar payloads and unresolved lifetimes" do
    for type <- [
          %{"Ref" => ["Erased", scalar(), "Mut"]},
          %{"Ref" => [%{"Var" => %{"Free" => 0}}, scalar(), "Shared"]},
          %{"Ref" => ["Erased", %{"Adt" => %{"id" => 0}}, "Shared"]},
          scalar()
        ] do
      assert_raise ArgumentError, ~r/constant initializer/, fn ->
        LLBC.audit!(promoted(type), ["first_party"])
      end
    end

    document =
      promoted(%{"Ref" => ["Erased", scalar(), "Shared"]})
      |> put_in(["translated", "global_decls", Access.at(0), "item_meta", "name"], name("read"))

    assert_raise ArgumentError, ~r/constant initializer/, fn ->
      LLBC.audit!(document, ["first_party"])
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
