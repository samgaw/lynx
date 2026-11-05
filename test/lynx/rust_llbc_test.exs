defmodule Lynx.Rust.LLBCTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.LLBC

  defp function do
    %{
      "def_id" => 0,
      "item_meta" => %{
        "name" => [%{"Ident" => ["first_party", 0]}, %{"Ident" => ["compute", 0]}],
        "opacity" => "Transparent"
      },
      "body" => %{"Structured" => %{}},
      "signature" => %{
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [%{"Value" => [0, %{"Scalar" => "Bool"}]}],
        "output" => %{"Deduplicated" => 0}
      }
    }
  end

  defp document(functions) do
    %{
      "charon_version" => "0.1.304",
      "has_errors" => false,
      "translated" => %{
        "crate_name" => "first_party",
        "fun_decls" => functions,
        "type_decls" => [],
        "global_decls" => [],
        "files" => [],
        "trait_decls" => [%{"Value" => [0, %{"some_trait" => true}]}]
      }
    }
  end

  defp translation do
    %{
      "charon_version" => "0.1.304",
      "aeneas_version" => "nightly-2026.11.04-2b9e3ea",
      "crate" => "first_party",
      "functions" => [
        %{
          "def_id" => 0,
          "is_opaque" => false,
          "lean_name" => "first_party.compute",
          "rust_name" => "first_party::compute"
        }
      ]
    }
  end

  test "links extracted identities and separates hash-cons families" do
    audit = LLBC.audit!(document([function()]), ["first_party"])
    assert {["bool"], "bool"} = LLBC.signature!(function(), audit)
    assert %{0 => %{"lean_name" => "first_party.compute"}} = LLBC.link!(audit, translation())
  end

  test "composite signatures retain tuple structure and require the standard Result identity" do
    boolean = %{"Value" => [0, %{"Scalar" => "Bool"}]}

    generics = fn types ->
      %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}
    end

    tuple = %{
      "Value" => [
        1,
        %{
          "Adt" => %{
            "id" => 0,
            "builtin" => "Tuple",
            "generics" => generics.([boolean, %{"Deduplicated" => 0}])
          }
        }
      ]
    }

    result = %{
      "Value" => [
        2,
        %{
          "Adt" => %{
            "id" => 42,
            "builtin" => nil,
            "generics" => generics.([%{"Deduplicated" => 1}, %{"Deduplicated" => 0}])
          }
        }
      ]
    }

    function =
      function()
      |> put_in(["signature", "inputs"], [tuple])
      |> put_in(["signature", "output"], result)

    result_decl = %{
      "def_id" => 42,
      "generics" => %{
        "regions" => [],
        "types" => [%{"index" => 0}, %{"index" => 1}],
        "const_generics" => [],
        "trait_clauses" => [],
        "outlives" => [],
        "trait_type_constraints" => []
      },
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["core", 0]},
          %{"Ident" => ["result", 0]},
          %{"Ident" => ["Result", 0]}
        ]
      },
      "kind" => %{
        "Enum" => [
          %{
            "id" => 0,
            "name" => "Ok",
            "fields" => [%{"ty" => %{"Value" => [3, %{"TypeVar" => %{"Free" => 0}}]}}],
            "discriminant" => %{"Signed" => ["Isize", "0"]}
          },
          %{
            "id" => 1,
            "name" => "Err",
            "fields" => [%{"ty" => %{"Value" => [4, %{"TypeVar" => %{"Free" => 1}}]}}],
            "discriminant" => %{"Signed" => ["Isize", "1"]}
          }
        ]
      }
    }

    doc = document([function]) |> put_in(["translated", "type_decls"], [result_decl])
    audit = LLBC.audit!(doc, ["first_party"])

    assert {[%{"tuple" => ["bool", "bool"]}],
            %{"result" => [%{"tuple" => ["bool", "bool"]}, "bool"]}} =
             LLBC.signature!(function, audit)

    for invalid <- [
          nil,
          %{result_decl | "kind" => "Opaque"},
          update_in(result_decl, ["kind", "Enum"], &Enum.reverse/1),
          update_in(result_decl, ["kind", "Enum"], fn [ok, err] ->
            [%{ok | "fields" => err["fields"]}, %{err | "fields" => ok["fields"]}]
          end),
          put_in(result_decl, ["item_meta", "name"], [
            %{"Ident" => ["other_crate", 0]},
            %{"Ident" => ["Result", 0]}
          ])
        ] do
      changed = put_in(doc, ["translated", "type_decls"], [invalid])

      assert_raise ArgumentError, ~r/unsupported NIF ADT identity/, fn ->
        LLBC.signature!(function, LLBC.audit!(changed, ["first_party"]))
      end
    end
  end

  test "rejects absent bodies and unsupported first-party implementations" do
    for body <- ["Opaque", "Missing", nil] do
      assert_raise CompileError, ~r/missing or unsupported first-party implementation/, fn ->
        LLBC.audit!(document([%{function() | "body" => body}]), ["first_party"])
      end
    end

    unsafe = put_in(function(), ["signature", "is_unsafe"], true)
    assert_raise CompileError, fn -> LLBC.audit!(document([unsafe]), ["first_party"]) end

    assert_raise ArgumentError, ~r/incomplete LLBC/, fn ->
      LLBC.audit!(%{document([function()]) | "has_errors" => true}, ["first_party"])
    end
  end

  test "rejects missing, opaque and inconsistent extraction dependencies" do
    audit = LLBC.audit!(document([function()]), ["first_party"])

    for translated <- [
          put_in(translation(), ["functions"], []),
          put_in(translation(), ["functions"], [%{"def_id" => 0, "is_opaque" => true}])
        ] do
      assert_raise CompileError, ~r/missing, ambiguous or opaque/, fn ->
        LLBC.link!(audit, translated)
      end
    end

    assert_raise ArgumentError, ~r/does not match/, fn ->
      LLBC.link!(audit, %{translation() | "crate" => "other"})
    end

    assert_raise ArgumentError, ~r/duplicate LLBC/, fn ->
      LLBC.audit!(document([function(), function()]), ["first_party"])
    end
  end

  test "unproved externals, indirect calls and ignored destructors cannot become native semantics" do
    for operation <- [
          %{"Call" => %{"call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => 99}}}}}},
          %{"Call" => %{"call" => %{"func" => %{"Move" => %{}}}}},
          %{"Drop" => %{}},
          %{"Global" => %{}}
        ] do
      function = put_in(function(), ["body", "Structured"], operation)
      assert_raise CompileError, fn -> LLBC.audit!(document([function]), ["first_party"]) end
    end
  end

  test "missing body diagnostics retain the Rust source location" do
    function =
      function()
      |> Map.put("body", "Missing")
      |> put_in(["item_meta", "span"], %{
        "Untagged" => %{"data" => %{"file_id" => 0, "beg" => %{"line" => 12, "col" => 3}}}
      })

    doc =
      put_in(document([function]), ["translated", "files"], [
        %{"id" => 0, "name" => %{"Local" => "src/lib.rs"}}
      ])

    error = assert_raise CompileError, fn -> LLBC.audit!(doc, ["first_party"]) end
    assert %{file: "src/lib.rs", line: 12} = error
  end
end
