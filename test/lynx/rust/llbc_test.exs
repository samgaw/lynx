defmodule Lynx.Rust.LLBCTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.LLBC

  @effectful_backend "nightly-2026.11.04-2b9e3ea+lynx-result-monad-v1+assertion-unwind-v1+global-names-v1+immediate-futures-v1+workspace-roots-v1+undefined-behavior-v1+native-loops-v1+effectful-calls-v1"

  test "Cargo dependencies cannot masquerade as standard model crates" do
    library = fn name -> %{"name" => name, "kind" => ["lib"]} end

    workspace = %{
      crates: [%{id: "first", targets: [library.("first_party")]}],
      packages: %{
        "first" => %{"targets" => [library.("first_party")]},
        "foreign" => %{"targets" => [library.("other")]}
      }
    }

    assert ["first_party"] = LLBC.crate_names!(workspace)

    for name <- ~w(core alloc std proc_macro test) do
      invalid = put_in(workspace, [:packages, "foreign", "targets"], [library.(name)])

      assert_raise ArgumentError, ~r/ambiguous Rust crate name/, fn ->
        LLBC.crate_names!(invalid)
      end
    end
  end

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

  test "accepts only the explicitly pinned Aeneas builds" do
    audit = LLBC.audit!(document([function()]), ["first_party"])

    assert %{0 => %{"lean_name" => "first_party.compute"}} =
             LLBC.link!(audit, %{
               translation()
               | "aeneas_version" => "nightly-2026.11.04-2b9e3ea+lynx-static-loans-v1"
             })

    assert %{0 => %{"lean_name" => "first_party.compute"}} =
             LLBC.link!(audit, %{translation() | "aeneas_version" => "build-2b9e3ea"})

    unmodified =
      translation()
      |> Map.put("aeneas_version", "build-2b9e3ea")
      |> Map.put("result_monad", "Lynx.NativeM")
      |> Map.put("effectful_calls_preserved", true)

    assert_raise ArgumentError, ~r/preserved call provenance/, fn ->
      LLBC.link!(audit, unmodified, result_monad: "Lynx.NativeM")
    end

    for version <- ["2b9e3ea4662b-dirty", "nightly-2026.11.04-2b9e3ea+unknown", nil] do
      assert_raise ArgumentError, ~r/does not match/, fn ->
        LLBC.link!(audit, %{translation() | "aeneas_version" => version})
      end
    end
  end

  test "binds translation provenance to the selected result monad" do
    audit = LLBC.audit!(document([function()]), ["first_party"])

    pure =
      Map.put(translation(), "aeneas_version", "nightly-2026.11.04-2b9e3ea+lynx-result-monad-v1")

    pure = Map.put(pure, "result_monad", "RustM")

    native =
      pure
      |> Map.put("result_monad", "Lynx.NativeM")
      |> Map.put("aeneas_version", @effectful_backend)
      |> Map.put("effectful_calls_preserved", true)

    assert %{0 => _} = LLBC.link!(audit, pure)
    assert %{0 => _} = LLBC.link!(audit, native, result_monad: "Lynx.NativeM")

    assert %{0 => _} =
             LLBC.link!(
               audit,
               Map.put(
                 native,
                 "aeneas_version",
                 @effectful_backend <> "+partial-discriminants-v1"
               ),
               result_monad: "Lynx.NativeM"
             )

    for {translation, expected} <- [
          {native, "RustM"},
          {Map.delete(pure, "result_monad"), "RustM"},
          {pure, "Lynx.NativeM"},
          {Map.put(native, "result_monad", "UncheckedM"), "UncheckedM"},
          {Map.put(native, "aeneas_version", "nightly-2026.11.04-2b9e3ea"), "Lynx.NativeM"}
        ] do
      assert_raise ArgumentError, fn ->
        LLBC.link!(audit, translation, result_monad: expected)
      end
    end
  end

  test "rejects runtime extraction without preserved effectful-call provenance" do
    audit = LLBC.audit!(document([function()]), ["first_party"])

    native =
      translation()
      |> Map.put("aeneas_version", @effectful_backend)
      |> Map.put("result_monad", "Lynx.NativeM")
      |> Map.put("effectful_calls_preserved", true)

    for invalid <- [
          Map.delete(native, "effectful_calls_preserved"),
          Map.put(native, "effectful_calls_preserved", false),
          Map.put(
            native,
            "aeneas_version",
            String.replace_suffix(@effectful_backend, "+effectful-calls-v1", "")
          )
        ] do
      assert_raise ArgumentError, ~r/effectful-calls-v1/, fn ->
        LLBC.link!(audit, invalid, result_monad: "Lynx.NativeM")
      end
    end
  end

  test "binds assertion unwind provenance to the explicit extraction mode" do
    audit = LLBC.audit!(document([function()]), ["first_party"])

    native =
      translation()
      |> Map.put(
        "aeneas_version",
        @effectful_backend
      )
      |> Map.put("effectful_calls_preserved", true)
      |> Map.put("result_monad", "Lynx.NativeM")
      |> Map.put("assertion_unwind_input", true)

    assert %{0 => _} =
             LLBC.link!(audit, native, result_monad: "Lynx.NativeM", assertion_unwind_input: true)

    global_names = native

    assert %{0 => _} =
             LLBC.link!(audit, global_names,
               result_monad: "Lynx.NativeM",
               assertion_unwind_input: true
             )

    assert_raise ArgumentError, ~r/assertion unwind input/, fn ->
      LLBC.link!(audit, global_names, result_monad: "Lynx.NativeM", assertion_unwind_input: false)
    end

    for {model, expected} <- [
          {native, false},
          {Map.delete(native, "assertion_unwind_input"), true},
          {Map.put(native, "assertion_unwind_input", "true"), true}
        ] do
      assert_raise ArgumentError, ~r/assertion unwind input/, fn ->
        LLBC.link!(audit, model, result_monad: "Lynx.NativeM", assertion_unwind_input: expected)
      end
    end
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

  test "byte-vector NIF types require actual alloc Vec identity and u8 elements" do
    args = %{
      "regions" => [],
      "types" => [%{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}],
      "const_generics" => [],
      "trait_refs" => []
    }

    vector = %{"Adt" => %{"id" => 5, "builtin" => nil, "generics" => args}}

    declaration = %{
      "def_id" => 5,
      "kind" => "Opaque",
      "item_meta" => %{"name" => Enum.map(~w(alloc vec Vec), &%{"Ident" => [&1, 0]})},
      "generics" => %{
        "regions" => [],
        "types" => [%{"index" => 0}],
        "const_generics" => [],
        "trait_clauses" => [],
        "outlives" => [],
        "trait_type_constraints" => []
      }
    }

    audit = %{references: %{}, translated: %{"type_decls" => [declaration]}}
    assert %{"vec" => "u8"} = LLBC.nif_type!(vector, audit)

    assert_raise ArgumentError, ~r/unsupported NIF ADT identity/, fn ->
      LLBC.nif_type!(put_in(vector, ["Adt", "generics", "types"], [%{"Scalar" => "Bool"}]), audit)
    end

    for changed <- [
          put_in(declaration, ["item_meta", "name"], [%{"Ident" => ["ShadowVec", 0]}]),
          put_in(declaration, ["kind"], %{"Struct" => []}),
          put_in(declaration, ["generics", "types"], [])
        ] do
      assert_raise ArgumentError, ~r/unsupported NIF ADT identity/, fn ->
        LLBC.nif_type!(vector, put_in(audit, [:translated, "type_decls"], [changed]))
      end
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

  test "unverified call diagnostics identify the foreign callee" do
    call = %{"Call" => %{"call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => 99}}}}}}
    caller = put_in(function(), ["body", "Structured"], call)

    foreign = %{
      "def_id" => 99,
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["core", 0]},
          %{"Ident" => ["result", 0]},
          %{"Impl" => %{"Trait" => 6}},
          %{"Ident" => ["branch", 0]}
        ]
      },
      "body" => "Opaque"
    }

    assert_raise CompileError,
                 ~r/unverified external Rust call core::result::\{impl\}::branch/,
                 fn ->
                   LLBC.audit!(document([caller, foreign]), ["first_party"])
                 end
  end

  test "unverified calls are diagnosed before their unsupported cleanup" do
    call = %{"Call" => %{"call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => 99}}}}}}
    body = %{"statements" => [%{"kind" => call}, %{"kind" => %{"Drop" => %{}}}]}
    caller = put_in(function(), ["body", "Structured"], body)

    assert_raise CompileError, ~r/unverified external Rust call/, fn ->
      LLBC.audit!(document([caller]), ["first_party"])
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

  test "links loop bodies to one Rust entrypoint and rejects inconsistent helper dependencies" do
    audit = LLBC.audit!(document([function()]), ["first_party"])
    [parent] = translation()["functions"]
    parent = Map.put(parent, "lean_file", "Example/Funs.lean")

    body =
      parent
      |> Map.put("lean_name", "first_party.compute_loop.body")
      |> Map.put("parent_lean_name", parent["lean_name"])
      |> Map.put("loop", %{"id" => 0, "pos" => [0], "is_body" => true})

    loop =
      body
      |> Map.put("lean_name", "first_party.compute_loop")
      |> put_in(["loop", "is_body"], false)

    translated = Map.put(translation(), "functions", [body, loop, parent])

    assert %{0 => %{"lean_name" => "first_party.compute", "loop_helpers" => [^body, ^loop]}} =
             LLBC.link!(audit, translated)

    old_native =
      translated
      |> Map.put("result_monad", "Lynx.NativeM")
      |> Map.put(
        "aeneas_version",
        "nightly-2026.11.04-2b9e3ea+lynx-result-monad-v1+assertion-unwind-v1+global-names-v1+immediate-futures-v1+workspace-roots-v1+undefined-behavior-v1"
      )

    assert_raise ArgumentError, ~r/effectful-calls-v1/, fn ->
      LLBC.link!(audit, old_native, result_monad: "Lynx.NativeM")
    end

    for invalid <- [
          [body, parent],
          [body, body, parent],
          [Map.put(body, "is_opaque", true), loop, parent],
          [Map.put(body, "parent_lean_name", "another.function"), loop, parent],
          [Map.put(body, "rust_name", "another::function"), loop, parent],
          [Map.put(body, "lean_file", "Other.lean"), loop, parent],
          [put_in(body, ["loop", "id"], -1), loop, parent],
          [put_in(body, ["loop", "pos"], [1]), loop, parent]
        ] do
      assert_raise ArgumentError, ~r/Aeneas loop/, fn ->
        LLBC.link!(audit, Map.put(translated, "functions", invalid))
      end
    end
  end
end
