defmodule Lynx.Rust.FileModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.FileModels

  test "file models require explicit runtime admission" do
    assert FileModels.enabled!(:reject, :pure) == []
    assert FileModels.enabled!(:reject, :runtime) == []
    assert FileModels.enabled!(:regular, :runtime) == [:native_files]

    assert_raise ArgumentError, ~r/require runtime/, fn ->
      FileModels.enabled!(:regular, :pure)
    end

    assert_raise ArgumentError, ~r/unsupported Rust file model/, fn ->
      FileModels.enabled!(:all, :runtime)
    end

    assert FileModels.type_models([], "Disk.Extraction") == []
  end

  defp parameters(regions \\ []),
    do: %{
      "regions" => Enum.map(regions, &%{"index" => &1}),
      "types" => [],
      "const_generics" => [],
      "trait_clauses" => [],
      "outlives" => [],
      "trait_type_constraints" => []
    }

  defp arguments(types),
    do: %{"types" => types, "regions" => [], "const_generics" => [], "trait_refs" => []}

  defp name(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp adt(id, types \\ []),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments(types)}}

  defp sync_fixture do
    types =
      for {id, path} <- [{1, ~w(std fs File)}, {2, ~w(core io error Error)}],
          do: %{
            "def_id" => id,
            "src" => "Normal",
            "kind" => "Opaque",
            "generics" => parameters(),
            "item_meta" => %{"name" => name(path)}
          }

    result = %{
      "def_id" => 3,
      "item_meta" => %{"name" => name(~w(core result Result))},
      "generics" => %{parameters() | "types" => [%{"index" => 0}, %{"index" => 1}]},
      "kind" => %{
        "Enum" =>
          for(
            {id, variant} <- [{0, "Ok"}, {1, "Err"}],
            do: %{
              "id" => id,
              "name" => variant,
              "fields" => [%{"ty" => %{"TypeVar" => %{"Free" => id}}}],
              "discriminant" => %{"Signed" => ["Isize", Integer.to_string(id)]}
            }
          )
      }
    }

    function = %{
      "def_id" => 4,
      "body" => "Opaque",
      "src" => "Normal",
      "generics" => parameters([0]),
      "item_meta" => %{
        "name" =>
          name(~w(std fs)) ++
            [
              %{
                "Impl" => %{
                  "Ty" => %{
                    "kind" => "InherentImplBlock",
                    "params" => parameters(),
                    "skip_binder" => adt(1)
                  }
                }
              },
              %{"Ident" => ["sync_all", 0]}
            ]
      },
      "signature" => %{
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [%{"Ref" => [%{"Var" => %{"Free" => 0}}, adt(1), "Shared"]}],
        "output" =>
          adt(3, [
            %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => arguments([])}},
            adt(2)
          ])
      }
    }

    {function, %{"type_decls" => types ++ [result]}}
  end

  test "standard file admission checks signatures and canonical type identities" do
    {function, translated} = sync_fixture()

    assert %{lean: "Lynx.NativeFile.syncAll", native_cutoff_only: true} =
             FileModels.resolve(function, translated, %{})

    for altered <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "is_variadic"], true),
          put_in(function, ["signature", "inputs"], []),
          put_in(function, ["generics", "types"], [%{"index" => 0}]),
          put_in(function, ["generics", "regions"], []),
          put_in(function, ["item_meta", "name"], name(~w(std fs sync_all))),
          Map.put(function, "body", %{"Structured" => %{}})
        ],
        do: assert(is_nil(FileModels.resolve(altered, translated, %{})))

    [file | rest] = translated["type_decls"]

    for altered <- [
          Map.put(file, "kind", %{"Struct" => []}),
          Map.put(file, "src", "TraitImpl"),
          put_in(file, ["item_meta", "name"], name(~w(other fs File)))
        ] do
      assert is_nil(FileModels.resolve(function, %{"type_decls" => [altered | rest]}, %{}))
    end

    assert is_nil(FileModels.resolve(function, %{"type_decls" => [file, file | rest]}, %{}))
  end
end
