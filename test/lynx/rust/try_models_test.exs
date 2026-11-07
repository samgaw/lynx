defmodule Lynx.Rust.TryModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.TryModels
  @fixture Path.expand("../../fixtures/rust_io/try_metadata.json", __DIR__)

  # Trimmed compiler metadata exercises admission; implementation properties are
  # checked separately against fresh Cargo extraction in FileOpenTest.
  defp fixture, do: @fixture |> File.read!() |> JSON.decode!()

  test "reuses only the exact standard Result/Try and identity conversion primitives" do
    translated = fixture()
    assert Enum.map(translated["fun_decls"], & &1["def_id"]) == [24, 25, 30]

    for function <- translated["fun_decls"] do
      assert %{builtin: true, native_transfer: true} =
               TryModels.resolve(function, translated, %{})

      for changed <- [
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "abi"], "C"),
            put_in(function, ["signature", "inputs"], []),
            put_in(function, ["src", "TraitImpl", "reuses_default"], true),
            Map.put(function, "def_id", 999)
          ] do
        assert is_nil(TryModels.resolve(changed, translated, %{}))
      end
    end
  end

  test "residual conversion must use the actual concrete identity dictionary" do
    translated = fixture()
    residual = Enum.find(translated["fun_decls"], &(&1["def_id"] == 25))
    model = TryModels.resolve(residual, translated, %{})
    error_type = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}

    args = fn types ->
      %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}
    end

    dictionary = %{
      "kind" => %{"TraitImpl" => %{"id" => 8, "generics" => args.([error_type])}},
      "trait_decl_ref" => %{"id" => 4, "generics" => args.([error_type, error_type])}
    }

    call = fn dict ->
      %{
        "body" => %{
          "Regular" => %{
            "kind" => %{"Fun" => 25},
            "generics" => %{
              args.([error_type, error_type, error_type])
              | "trait_refs" => [
                  %{"regions" => [], "outlives" => [], "skip_binder" => %{"Value" => [100, dict]}}
                ]
            }
          }
        }
      }
    end

    assert {:ok, %{25 => [30]}} =
             TryModels.audit([call.(dictionary)], %{25 => model}, translated, %{})

    for changed <- [
          put_in(dictionary, ["kind", "TraitImpl", "id"], 999),
          put_in(dictionary, ["trait_decl_ref", "id"], 999),
          put_in(dictionary, ["kind", "TraitImpl", "generics"], args.([])),
          Map.put(dictionary, "kind", %{"Clause" => [%{"Free" => 0}, %{"regions" => []}]})
        ] do
      assert {:error, _, message} =
               TryModels.audit([call.(changed)], %{25 => model}, translated, %{})

      assert message =~ "concrete standard identity From"
    end

    missing =
      Map.update!(translated, "fun_decls", &Enum.reject(&1, fn f -> f["def_id"] == 30 end))

    assert {:error, _, _} = TryModels.audit([call.(dictionary)], %{25 => model}, missing, %{})
  end

  test "a changed ControlFlow payload cannot inherit branch semantics" do
    translated = fixture()
    branch = hd(translated["fun_decls"])

    changed =
      Map.update!(translated, "type_decls", fn types ->
        Enum.map(types, fn
          %{"def_id" => 9} = type -> put_in(type, ["kind", "Enum", Access.at(0), "fields"], [])
          type -> type
        end)
      end)

    assert is_nil(TryModels.resolve(branch, changed, %{}))
  end
end
