defmodule Lynx.Rustler.TextInputBindingsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.Bindings
  @snapshot Path.expand("../../fixtures/rustler/text_inputs.json", __DIR__)

  setup do
    %{"document" => document, "bindings" => bindings} = JSON.decode!(File.read!(@snapshot))
    %{document: document, manifest: %{bindings: bindings}}
  end

  test "resolves compiled String inputs inside tuples and options", ctx do
    assert %{
             bindings: [
               %{"arguments" => ["string", "bool"], "result" => "string"},
               %{"arguments" => ["string"], "result" => "bool"},
               %{
                 "arguments" => [%{"tuple" => [%{"option" => "string"}, "bool"]}],
                 "result" => %{"tuple" => [%{"option" => "string"}, "bool"]}
               }
             ]
           } = Bindings.resolve!(ctx.manifest, ctx.document, ["experiment_nif"])
  end

  test "rejects lookalike String input identities and changed argument types", ctx do
    for alteration <- [:identity, :argument] do
      document =
        case alteration do
          :identity ->
            update_in(ctx.document, ["translated", "type_decls"], fn types ->
              Enum.map(types, fn type ->
                if type["item_meta"]["lang_item"] == "String",
                  do:
                    put_in(type, ["item_meta", "name"], [
                      %{"Ident" => ["other", 0]},
                      %{"Ident" => ["String", 0]}
                    ]),
                  else: type
              end)
            end)

          :argument ->
            put_in(
              ctx.document,
              ["translated", "fun_decls", Access.at(0), "signature", "inputs", Access.at(0)],
              %{"Scalar" => "Bool"}
            )
        end

      assert_raise ArgumentError, fn ->
        Bindings.resolve!(ctx.manifest, document, ["experiment_nif"])
      end
    end
  end

  test "reports argument decoding independently of String result encoding", ctx do
    %{bindings: [_, binding, _]} =
      Bindings.resolve!(ctx.manifest, ctx.document, ["experiment_nif"])

    assert [boundary] = Bindings.codec_boundaries(%{bindings: [binding]}, "0.39.0")
    assert boundary =~ "String Decoder model"
    assert boundary =~ "oversized slices exhaust verification"
    assert boundary =~ "unverified"
    refute boundary =~ "Encoder"

    assert_raise ArgumentError, ~r/destructor-free value codecs/, fn ->
      Bindings.validate_ownership!(%{bindings: [binding]}, :explicit)
    end
  end
end
