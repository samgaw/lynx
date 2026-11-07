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

  test "close-only extraction admits the File type without inventing an I/O error dependency" do
    assert [%{rust: "std::fs::File", lean: "Lynx.NativeFile", import: "Close.NativeRuntime"}] =
             FileModels.type_models([{0, %{native_file_types: {1, nil}}}], "Close.Extraction")

    assert [%{rust: "std::fs::File"}, %{rust: "core::io::error::Error"}] =
             FileModels.type_models(
               [{0, %{native_file_types: {1, nil}}}, {1, %{native_file_types: {1, 2}}}],
               "Close.Extraction"
             )
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

  test "set_len validates its inherent method and actual argument and result widths" do
    {sync, translated} = sync_fixture()
    path = Enum.drop(sync["item_meta"]["name"], -1) ++ [%{"Ident" => ["set_len", 0]}]

    function =
      sync
      |> put_in(["item_meta", "name"], path)
      |> put_in(
        ["signature", "inputs"],
        sync["signature"]["inputs"] ++
          [
            %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
          ]
      )

    assert %{lean: "Lynx.NativeFile.setLen", native_cutoff_only: true} =
             FileModels.resolve(function, translated, %{})

    for altered <- [
          put_in(function, ["signature", "inputs", Access.at(1)], %{
            "Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}
          }),
          put_in(function, ["signature", "inputs", Access.at(0)], %{
            "Ref" => [%{"Var" => %{"Free" => 0}}, adt(1), "Mut"]
          }),
          put_in(function, ["signature", "output"], adt(3, [adt(1), adt(2)])),
          put_in(
            function,
            ["item_meta", "name", Access.at(2), "Impl", "Ty", "skip_binder"],
            adt(2)
          ),
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["item_meta", "name", Access.at(3)], %{"Ident" => ["set_len", 1]})
        ],
        do: assert(is_nil(FileModels.resolve(altered, translated, %{})))
  end
end
