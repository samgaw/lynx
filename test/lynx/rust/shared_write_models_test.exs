defmodule Lynx.Rust.SharedWriteModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{FileModels, CallModels}
  @fixture Path.expand("../../fixtures/rust_effects/shared_write_metadata.json", __DIR__)

  defp fixture, do: File.read!(@fixture) |> JSON.decode!()

  test "the actual shared File write declaration preserves identity under explicit file admission" do
    t = fixture()
    [function] = t["fun_decls"]

    assert %{native_file_types: {9, 8}, lean: "Lynx.NativeFile.write", native_cutoff_only: true} =
             FileModels.resolve(function, t, %{})

    assert %{27 => %{implementation_verified: false, status: :modelled}} =
             CallModels.resolve([function], t, %{}, [:native_files], :runtime)

    assert CallModels.resolve([function], t, %{}, [], :runtime) == %{}
    assert CallModels.resolve([function], t, %{}, [:native_files], :pure) == %{}
  end

  test "different signatures, ownership, lifetime or method identities are rejected" do
    t = fixture()
    [function] = t["fun_decls"]

    for changed <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "inputs"], []),
          put_in(function, ["signature", "output"], %{
            "Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}
          }),
          put_in(function, ["generics", "outlives"], []),
          put_in(function, ["generics", "regions"], []),
          put_in(function, ["src", "TraitImpl", "reuses_default"], true),
          put_in(function, ["src", "TraitImpl", "impl_ref", "generics", "regions"], []),
          put_in(function, ["item_meta", "name"], [%{"Ident" => ["third_party", 0]}]),
          Map.put(function, "body", %{"Structured" => %{}})
        ],
        do: assert(is_nil(FileModels.resolve(changed, t, %{})))

    for changed <- [
          put_in(t, ["trait_impls", Access.at(0), "is_unsafe"], true),
          put_in(t, ["trait_impls", Access.at(0), "is_negative"], true),
          put_in(t, ["trait_impls", Access.at(0), "generics", "regions"], []),
          put_in(t, ["trait_impls", Access.at(0), "methods"], []),
          put_in(
            t,
            ["trait_impls", Access.at(0), "methods", Access.at(0), "skip_binder", "id"],
            999
          ),
          put_in(t, ["trait_decls", Access.at(0), "item_meta", "name"], [
            %{"Ident" => ["FakeWrite", 0]}
          ])
        ],
        do: assert(is_nil(FileModels.resolve(function, changed, %{})))
  end
end
