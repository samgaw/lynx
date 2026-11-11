defmodule Lynx.Rustler.MapConstructorTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC, ResultModels}
  alias Lynx.Rustler.EncoderModels

  @snapshot JSON.decode!(
              File.read!(Path.expand("../../fixtures/rustler/map_constructor.json", __DIR__))
            )

  test "validates the compiled map constructor and both slice lifetime relations" do
    f = @snapshot["constructor"]
    t = @snapshot["translated"]

    assert %{lean: "Lynx.Rustler.Encoding.mapFromTermArrays", can_fail: true, lift: false} =
             EncoderModels.resolve(f, t, %{})

    [env, keys, values] = f["signature"]["inputs"]

    for changed <- [
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["signature", "is_variadic"], true),
          put_in(f, ["signature", "inputs"], [env, values, keys]),
          put_in(f, ["signature", "inputs"], [
            env,
            put_in(keys, ["Ref", Access.at(2)], "Mut"),
            values
          ]),
          put_in(f, ["signature", "output"], env),
          put_in(f, ["generics", "outlives"], []),
          update_in(f, ["generics", "regions"], &Enum.reverse/1),
          put_in(f, ["generics", "trait_clauses"], [%{}]),
          Map.put(f, "body", %{"Structured" => %{}}),
          Map.put(f, "src", %{"TraitImpl" => %{}})
        ],
        do: assert(is_nil(EncoderModels.resolve(changed, t, %{})))
  end

  test "unwrap validates Result identity and Debug without claiming error behavior" do
    f = @snapshot["unwrap"]
    t = @snapshot["translated"]

    assert %{encoder_unwrap_ok: true, keep_trait_clauses: [false], native_cutoff_only: true} =
             ResultModels.resolve_encoder_unwrap(f, t, %{})

    for changed <- [
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["signature", "output"], %{"TypeVar" => %{"Free" => 1}}),
          put_in(f, ["generics", "trait_clauses"], []),
          put_in(f, ["generics", "regions"], [%{"index" => 0}]),
          Map.put(f, "body", %{"Structured" => %{}})
        ],
        do: assert(is_nil(ResultModels.resolve_encoder_unwrap(changed, t, %{})))

    model = ResultModels.resolve_encoder_unwrap(f, t, %{}) |> Map.put(:function, f)
    doc = %{"translated" => Map.put(t, "fun_decls", [f])}
    {lowered, [id]} = ResultModels.lower_native_names!(doc, %{f["def_id"] => model})
    assert id == f["def_id"]

    assert [
             %{
               "item_meta" => %{
                 "name" => [
                   %{"Ident" => ["lynx_rustler", 0]},
                   %{"Ident" => ["result_unwrap_ok", 0]}
                 ]
               }
             }
           ] = lowered["translated"]["fun_decls"]

    assert_raise ArgumentError, ~r/missing audited/, fn ->
      ResultModels.lower_native_names!(put_in(doc, ["translated", "fun_decls"], []), %{
        id => model
      })
    end
  end

  test "unused error Debug only supports elaboration of a discarded dictionary" do
    f = @snapshot["debug"]
    t = @snapshot["translated"]

    assert %{elaboration_only: true, native_cutoff_only: true} =
             EncoderModels.resolve(f, t, %{})

    for changed <- [
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["src", "TraitImpl", "reuses_default"], true),
          Map.put(f, "def_id", 999),
          Map.put(f, "body", %{"Structured" => %{}})
        ],
        do: assert(is_nil(EncoderModels.resolve(changed, t, %{})))
  end

  test "the closed audit rejects callable uses of the error formatter" do
    debug = @snapshot["debug"]

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
      Map.merge(@snapshot["translated"], %{
        "crate_name" => "first_party",
        "global_decls" => [],
        "files" => [],
        "fun_decls" => [caller, debug]
      })

    assert %{31 => %{elaboration_only: true}} =
             CallModels.resolve([debug], t, %{}, [:rustler_encoders])

    assert_raise CompileError, ~r/unverified external Rust call/, fn ->
      LLBC.audit!(
        %{"charon_version" => "0.1.304", "has_errors" => false, "translated" => t},
        ["first_party"],
        external_calls: [:rustler_encoders]
      )
    end
  end
end
