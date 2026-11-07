defmodule Lynx.Rust.FileOpenModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.FileOpenModels

  test "standard borrowed path conversion preserves its exact signature and method identity" do
    {function, translated} = conversion_fixture()

    assert %{lean: "Lynx.NativeFile.asRefStr", lift: true} =
             FileOpenModels.resolve(function, translated, %{})

    for changed <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "inputs"], [reference(1, string())]),
          put_in(function, ["signature", "inputs"], [reference(0, adt(3))]),
          put_in(function, ["signature", "output"], reference(1, adt(3))),
          put_in(function, ["generics", "regions"], []),
          put_in(function, ["generics", "types"], [%{"index" => 0}]),
          put_in(function, ["src", "TraitImpl", "reuses_default"], true),
          Map.put(function, "def_id", 99)
        ] do
      translated = Map.put(translated, "fun_decls", [changed])
      assert is_nil(FileOpenModels.resolve(changed, translated, %{}))
    end

    [impl] = translated["trait_impls"]

    for changed <- [
          Map.put(impl, "methods", []),
          Map.put(impl, "methods", impl["methods"] ++ impl["methods"]),
          put_in(impl, ["impl_trait", "generics"], args([adt(3), adt(3)])),
          put_in(impl, ["item_meta", "name"], name(~w(other path))),
          Map.put(impl, "is_unsafe", true)
        ] do
      assert is_nil(
               FileOpenModels.resolve(
                 function,
                 Map.put(translated, "trait_impls", [changed]),
                 %{}
               )
             )
    end
  end

  test "ambiguous canonical types cannot acquire standard path semantics" do
    {function, translated} = conversion_fixture()
    [path] = translated["type_decls"]

    assert is_nil(
             FileOpenModels.resolve(
               function,
               Map.put(translated, "type_decls", [path, path]),
               %{}
             )
           )
  end

  test "a custom or unresolved dictionary cannot be erased at an open call" do
    {_, translated} = conversion_fixture()
    models = %{1 => %{native_file_open: {3, 5}}}

    for dictionary <- [
          %{
            "kind" => %{"Clause" => [%{"Free" => 0}, %{"regions" => []}]},
            "trait_decl_ref" => %{"id" => 5, "generics" => args([string(), adt(3)])}
          },
          %{
            "kind" => %{"TraitImpl" => %{"id" => 7, "generics" => args([])}},
            "trait_decl_ref" => %{"id" => 5, "generics" => args([string(), adt(3)])}
          }
        ] do
      caller = %{
        "body" => %{
          "Regular" => %{
            "kind" => %{"Fun" => 1},
            "generics" => %{args([reference(0, string())]) | "trait_refs" => [dictionary]}
          }
        }
      }

      assert {:error, ^caller, message} =
               FileOpenModels.audit([caller], models, translated, %{})

      assert message =~ "concrete standard &str AsRef<Path>"
    end
  end

  defp conversion_fixture do
    impl_name = name(~w(std path)) ++ [%{"Impl" => %{"Trait" => 7}}]

    function = %{
      "def_id" => 25,
      "body" => "Opaque",
      "generics" => params(1),
      "item_meta" => %{"name" => impl_name ++ name(["as_ref"])},
      "src" => %{
        "TraitImpl" => %{
          "impl_ref" => %{"id" => 7, "generics" => args([])},
          "trait_ref" => %{"id" => 5, "generics" => args([string(), adt(3)])},
          "item_id" => 0,
          "reuses_default" => false
        }
      },
      "signature" => %{
        "abi" => "Rust",
        "is_unsafe" => false,
        "is_variadic" => false,
        "inputs" => [reference(0, string())],
        "output" => reference(0, adt(3))
      }
    }

    impl = %{
      "def_id" => 7,
      "src" => "Normal",
      "is_unsafe" => false,
      "is_negative" => false,
      "generics" => params(0),
      "item_meta" => %{"name" => impl_name},
      "impl_trait" => %{"id" => 5, "generics" => args([string(), adt(3)])},
      "methods" => [
        %{"kind" => %{"TraitMethod" => [5, 0]}, "skip_binder" => %{"id" => 25}}
      ],
      "types" => [],
      "consts" => [],
      "implied_trait_refs" => []
    }

    translated = %{
      "fun_decls" => [function],
      "trait_impls" => [impl],
      "trait_decls" => [
        %{"def_id" => 5, "item_meta" => %{"name" => name(~w(core convert AsRef))}}
      ],
      "type_decls" => [%{"def_id" => 3, "item_meta" => %{"name" => name(~w(std path Path))}}]
    }

    {function, translated}
  end

  defp params(regions),
    do: %{
      "regions" => for(index <- 0..(regions - 1)//1, do: %{"index" => index}),
      "types" => [],
      "trait_clauses" => [],
      "const_generics" => [],
      "trait_type_constraints" => [],
      "outlives" => []
    }

  defp args(types),
    do: %{"regions" => [], "types" => types, "trait_refs" => [], "const_generics" => []}

  defp name(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp adt(id), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args([])}}
  defp string, do: %{"Adt" => %{"id" => 5, "builtin" => "Str", "generics" => args([])}}
  defp reference(region, type), do: %{"Ref" => [%{"Var" => %{"Free" => region}}, type, "Shared"]}
end
