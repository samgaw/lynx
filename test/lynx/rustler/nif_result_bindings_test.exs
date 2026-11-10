defmodule Lynx.Rustler.NifResultBindingsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.Bindings
  @snapshot Path.expand("../../fixtures/rustler/nif_result.json", __DIR__)
  @models [%{rust: "rustler::term::Term", lean: "Lynx.Rustler.NativeTerm"}]

  setup do
    %{"document" => document, "bindings" => bindings} =
      @snapshot |> File.read!() |> JSON.decode!()

    %{document: document, manifest: %{bindings: bindings}}
  end

  test "resolves alias and explicit Result spelling against actual compiled Error", ctx do
    manifest =
      update_in(ctx.manifest, [:bindings], fn bindings ->
        Enum.map(bindings, fn b ->
          if b["name"] == "explicit_result",
            do: %{b | "result" => %{"result" => ["bool", %{"native" => ["rustler", "Error"]}]}},
            else: b
        end)
      end)

    resolved = Bindings.resolve!(manifest, ctx.document, ["experiment_nif"], @models)

    assert [
             %{"arguments" => ["term", "bool"], "result" => %{"nif_result" => "bool"}},
             %{"arguments" => ["term", "bool"], "result" => %{"nif_result" => "bool"}},
             %{"arguments" => ["term"], "result" => "term"}
           ] = resolved.bindings
  end

  test "rejects the same return alias with a different Error identity", ctx do
    document =
      update_in(ctx.document, ["translated", "type_decls"], fn types ->
        Enum.map(types, fn t ->
          if List.last(t["item_meta"]["name"]) == %{"Ident" => ["Error", 0]},
            do:
              put_in(t, ["item_meta", "name"], [
                %{"Ident" => ["other", 0]},
                %{"Ident" => ["Error", 0]}
              ]),
            else: t
        end)
      end)

    assert_raise ArgumentError, ~r/actual Rustler Error/, fn ->
      Bindings.resolve!(ctx.manifest, document, ["experiment_nif"], @models)
    end
  end

  test "keeps ordinary Result encoding distinct from Rustler's return specialization", ctx do
    [binding | _] = ctx.manifest.bindings
    binding = %{binding | "result" => %{"result" => ["bool", "u64"]}}
    [function | _] = ctx.document["translated"]["fun_decls"]
    output = function["signature"]["output"]
    [ok, _] = output["Adt"]["generics"]["types"]
    u64 = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
    function = put_in(function, ["signature", "output", "Adt", "generics", "types"], [ok, u64])
    document = put_in(ctx.document, ["translated", "fun_decls"], [function])

    assert %{bindings: [%{"result" => %{"result" => ["bool", "u64"]}}]} =
             Bindings.resolve!(%{bindings: [binding]}, document, ["experiment_nif"], @models)
  end

  test "requires the explicit native Term boundary and its compiled nominal identity", ctx do
    assert_raise ArgumentError, ~r/Term requires its explicit FFI/, fn ->
      Bindings.resolve!(ctx.manifest, ctx.document, ["experiment_nif"], [])
    end

    document =
      update_in(ctx.document, ["translated", "type_decls"], fn types ->
        Enum.map(types, fn t ->
          if List.last(t["item_meta"]["name"]) == %{"Ident" => ["Term", 0]},
            do:
              put_in(t, ["item_meta", "name"], [
                %{"Ident" => ["other", 0]},
                %{"Ident" => ["Term", 0]}
              ]),
            else: t
        end)
      end)

    assert_raise ArgumentError, ~r/unsupported lifetime-bearing NIF type/, fn ->
      Bindings.resolve!(ctx.manifest, document, ["experiment_nif"], @models)
    end
  end
end
