defmodule Lynx.Rust.ExpectModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, ResultModels}
  @fixture Path.expand("../../fixtures/rust_effects/expect_metadata.json", __DIR__)
  defp fixture, do: File.read!(@fixture) |> JSON.decode!()

  test "only the exact runtime expect declaration gets a guarded payload transfer" do
    t = fixture()
    [expect, _] = t["fun_decls"]

    assert %{
             native_expect_ok: true,
             native_transfer: true,
             native_cutoff_only: true,
             keep_trait_clauses: [false],
             lean: "Lynx.NativeM.expectOk"
           } =
             ResultModels.resolve_native_expect(expect, t, %{})

    assert CallModels.resolve([expect], t, %{}, [], :pure) == %{}

    for changed <- [
          put_in(expect, ["signature", "is_unsafe"], true),
          put_in(expect, ["signature", "abi"], "C"),
          put_in(expect, ["signature", "inputs"], []),
          put_in(expect, ["signature", "output"], %{"TypeVar" => %{"Free" => 1}}),
          put_in(expect, ["generics", "trait_clauses"], []),
          put_in(expect, ["generics", "types"], [%{"index" => 0}]),
          Map.put(expect, "body", %{"Structured" => %{}}),
          Map.put(expect, "src", "Unknown")
        ],
        do: assert(is_nil(ResultModels.resolve_native_expect(changed, t, %{})))

    altered =
      put_in(t, ["trait_decls", Access.at(0), "item_meta", "name"], [%{"Ident" => ["Fake", 0]}])

    assert is_nil(ResultModels.resolve_native_expect(expect, altered, %{}))
  end

  test "backend aliasing preserves audited identities and refuses bodies and collisions" do
    t = fixture()
    [expect, _] = t["fun_decls"]
    models = CallModels.resolve([expect], t, %{}, [], :runtime)
    doc = %{"translated" => t}
    assert {lowered, [22]} = ResultModels.lower_native_names!(doc, models)
    [aliased, _] = lowered["translated"]["fun_decls"]
    assert aliased["signature"] == expect["signature"]
    assert aliased["def_id"] == expect["def_id"]

    assert aliased["item_meta"]["name"] == [
             %{"Ident" => ["lynx_native", 0]},
             %{"Ident" => ["result_expect_ok", 0]}
           ]

    assert {^doc, []} = ResultModels.lower_native_names!(doc, %{})

    first_party =
      put_in(doc, ["translated", "fun_decls", Access.at(0), "body"], %{"Structured" => %{}})

    assert_raise ArgumentError, ~r/audited opaque declaration/, fn ->
      ResultModels.lower_native_names!(first_party, models)
    end

    collision = %{aliased | "def_id" => 999, "body" => %{"Structured" => %{}}}
    collided = update_in(doc, ["translated", "fun_decls"], &(&1 ++ [collision]))

    assert_raise ArgumentError, ~r/collides/, fn ->
      ResultModels.lower_native_names!(collided, models)
    end

    absent = put_in(doc, ["translated", "fun_decls"], [])

    assert_raise ArgumentError, ~r/missing audited/, fn ->
      ResultModels.lower_native_names!(absent, models)
    end
  end

  test "unused Debug dictionary support does not claim a formatting implementation" do
    t = fixture()
    [_, debug] = t["fun_decls"]

    assert %{elaboration_only: true, native_cutoff_only: true, lift: false} =
             ResultModels.resolve_unused_io_debug(debug, t, %{})

    for changed <- [
          put_in(debug, ["signature", "is_unsafe"], true),
          put_in(debug, ["signature", "inputs"], []),
          put_in(debug, ["src", "TraitImpl", "reuses_default"], true),
          Map.put(debug, "def_id", 999),
          Map.put(debug, "body", %{"Structured" => %{}})
        ],
        do: assert(is_nil(ResultModels.resolve_unused_io_debug(changed, t, %{})))
  end

  test "a direct call cannot use an elaboration-only Debug dictionary" do
    t = fixture()
    [_, debug] = t["fun_decls"]

    caller = %{
      "def_id" => 100,
      "item_meta" => %{
        "name" => [%{"Ident" => ["first_party", 0]}, %{"Ident" => ["format", 0]}],
        "opacity" => "Transparent"
      },
      "signature" => %{
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [],
        "output" => %{"Adt" => %{"builtin" => "Tuple", "generics" => %{"types" => []}}}
      },
      "body" => %{
        "Structured" => %{
          "Call" => %{
            "call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => debug["def_id"]}}}}
          }
        }
      }
    }

    t =
      Map.merge(t, %{
        "crate_name" => "first_party",
        "global_decls" => [],
        "files" => [],
        "fun_decls" => [caller | t["fun_decls"]]
      })

    assert %{30 => %{elaboration_only: true}} =
             CallModels.resolve([debug], t, %{}, [:native_files], :runtime)

    assert_raise CompileError, ~r/unverified external Rust call/, fn ->
      Lynx.Rust.LLBC.audit!(
        %{"charon_version" => "0.1.304", "has_errors" => false, "translated" => t},
        ["first_party"],
        execution: :runtime,
        external_calls: [:native_files]
      )
    end
  end
end
