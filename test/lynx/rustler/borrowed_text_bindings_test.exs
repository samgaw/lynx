defmodule Lynx.Rustler.BorrowedTextBindingsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LLBC, StringModels}
  alias Lynx.Rustler.Bindings
  @snapshot Path.expand("../../fixtures/rustler/borrowed_text.json", __DIR__)

  setup do
    %{"document" => document, "bindings" => bindings} = JSON.decode!(File.read!(@snapshot))
    [function | _] = document["translated"]["fun_decls"]

    %{
      document: document,
      manifest: %{bindings: bindings},
      input: hd(function["signature"]["inputs"])
    }
  end

  test "recognizes actual builtin str borrows and nested compiled signatures", ctx do
    translated = ctx.document["translated"]
    assert StringModels.borrowed_type?(ctx.input, translated, %{})
    assert LLBC.nif_type!(ctx.input, %{translated: translated, references: %{}}) == "str"

    assert %{
             bindings: [
               %{"arguments" => ["str"], "result" => "str"},
               %{"arguments" => ["str"], "result" => %{"option" => "u32"}},
               %{
                 "arguments" => [%{"tuple" => [%{"option" => "str"}, "bool"]}],
                 "result" => %{"tuple" => [%{"option" => "str"}, "bool"]}
               }
             ]
           } = Bindings.resolve!(ctx.manifest, ctx.document, ["experiment_nif"])
  end

  test "rejects mutable, static and nominal reference substitutions", ctx do
    [region, value, _] = ctx.input["Ref"]

    for changed <- [
          %{"Ref" => [region, value, "Mut"]},
          %{"Ref" => ["Static", value, "Shared"]},
          %{"Ref" => [region, put_in(value, ["Adt", "builtin"], nil), "Shared"]},
          %{"Ref" => [region, %{"Scalar" => "Bool"}, "Shared"]}
        ] do
      refute StringModels.borrowed_type?(changed, ctx.document["translated"], %{})

      assert_raise ArgumentError, ~r/shared builtin str/, fn ->
        LLBC.nif_type!(changed, %{translated: ctx.document["translated"], references: %{}})
      end
    end
  end

  test "requires the builtin byte-slice representation and reports both FFI directions", ctx do
    translated =
      update_in(ctx.document["translated"], ["type_decls"], fn types ->
        Enum.map(types, fn type ->
          if type["src"] == %{"Builtin" => "Str"},
            do: put_in(type, ["kind", "Struct", Access.at(0), "ty"], %{"Scalar" => "Bool"}),
            else: type
        end)
      end)

    refute StringModels.borrowed_type?(ctx.input, translated, %{})
    boundaries = Bindings.codec_boundaries(ctx.manifest, "0.39.0")
    assert Enum.any?(boundaries, &String.contains?(&1, "borrowed str Decoder"))
    assert Enum.any?(boundaries, &String.contains?(&1, "borrowed str Encoder"))
    assert Enum.all?(boundaries, &String.contains?(&1, "unverified"))

    assert_raise ArgumentError, ~r/destructor-free value codecs/, fn ->
      Bindings.validate_ownership!(%{bindings: [Enum.at(ctx.manifest.bindings, 1)]}, :explicit)
    end

    assert [] ==
             Bindings.codec_boundaries(
               %{
                 bindings: [
                   %{
                     "arguments" => [%{"native" => ["str"]}],
                     "result" => %{"resource" => ["str"]}
                   }
                 ]
               },
               "0.39.0"
             )
  end
end
