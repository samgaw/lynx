defmodule Lynx.Rust.NativeFileCodecTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeCodecs

  defp args(types),
    do: %{"types" => types, "regions" => [], "const_generics" => [], "trait_refs" => []}

  defp params,
    do:
      Map.merge(args([]), %{
        "trait_clauses" => [],
        "trait_type_constraints" => [],
        "outlives" => []
      })

  defp fixture do
    file = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args([])}}

    declaration = %{
      "def_id" => 1,
      "src" => "Normal",
      "kind" => "Opaque",
      "generics" => params(),
      "item_meta" => %{"name" => Enum.map(~w(std fs File), &%{"Ident" => [&1, 0]})}
    }

    function = %{
      "body" => %{
        "Regular" => %{
          "kind" => %{"Fun" => 10},
          "generics" => %{args([file]) | "regions" => [%{"Body" => 0}]}
        }
      }
    }

    %{
      functions: [function],
      external_calls: %{10 => %{native_codec_input: true}, 20 => %{native_file_types: {1, 2}}},
      references: %{},
      first_party: [],
      translated: %{"type_decls" => [declaration]}
    }
  end

  test "bare consuming inputs still require an admitted file capability" do
    audit = fixture()
    file = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args([])}}
    call = %{args([file]) | "trait_refs" => [%{}]}

    audit =
      audit
      |> put_in([:functions, Access.at(0), "body", "Regular", "generics"], call)
      |> put_in([:external_calls, 10], %{native_codec_drop: true})

    assert NativeCodecs.plan!(audit) == []

    assert_raise ArgumentError, ~r/unsupported native heap struct identity/, fn ->
      NativeCodecs.plan!(%{audit | external_calls: Map.delete(audit.external_calls, 20)})
    end
  end

  test "admits only the validated standard file capability as an opaque heap payload" do
    audit = fixture()
    assert NativeCodecs.plan!(audit) == []

    for altered <- [
          %{audit | external_calls: Map.delete(audit.external_calls, 20)},
          put_in(audit, [:external_calls, 20, :native_file_types], {2, 1}),
          put_in(audit, [:translated, "type_decls", Access.at(0), "src"], "Destruct"),
          put_in(audit, [:translated, "type_decls", Access.at(0), "kind"], %{"Struct" => []}),
          put_in(audit, [:translated, "type_decls", Access.at(0), "generics", "types"], [
            %{"index" => 0}
          ])
        ] do
      assert_raise ArgumentError, ~r/unsupported native heap struct identity/, fn ->
        NativeCodecs.plan!(altered)
      end
    end
  end

  test "error cleanup needs its own admitted identity and cannot borrow file admission" do
    audit = fixture()
    error = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args([])}}

    audit =
      audit
      |> put_in([:functions, Access.at(0), "body", "Regular", "generics"], %{
        args([error])
        | "trait_refs" => [%{}]
      })
      |> put_in([:external_calls, 10], %{native_codec_drop: true})
      |> put_in([:external_calls, 20], %{
        native_file_types: {nil, 1},
        native_io_error_drop: true
      })
      |> put_in(
        [:translated, "type_decls", Access.at(0), "item_meta", "name"],
        Enum.map(~w(core io error Error), &%{"Ident" => [&1, 0]})
      )

    assert NativeCodecs.plan!(audit) == []

    for altered <- [
          put_in(audit, [:external_calls, 20, :native_io_error_drop], false),
          put_in(audit, [:external_calls, 20, :native_file_types], {1, nil}),
          %{audit | external_calls: Map.delete(audit.external_calls, 20)},
          put_in(audit, [:translated, "type_decls", Access.at(0), "kind"], %{"Struct" => []})
        ] do
      assert_raise ArgumentError, ~r/unsupported native heap struct identity/, fn ->
        NativeCodecs.plan!(altered)
      end
    end
  end
end
