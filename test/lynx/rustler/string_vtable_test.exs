defmodule Lynx.Rustler.StringVtableTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LLBC, VTables}

  setup do
    document =
      Path.expand("../../fixtures/rustler/string_vtable.json", __DIR__)
      |> File.read!()
      |> JSON.decode!()

    translated = document["translated"]
    refs = LLBC.type_references!(document)
    [global] = VTables.foreign_globals(translated)
    {checked, _, _} = VTables.audit!([global], [], translated, refs)
    audited = checked[global["def_id"]]

    %{
      document: document,
      translated: translated,
      refs: refs,
      global: global,
      audited: audited,
      info: audited["lynx_vtable"]
    }
  end

  test "validates String encoding and deallocation without claiming a foreign implementation proof",
       ctx do
    assert %{
             model_method: "Lynx.Rustler.Encoding.string",
             methods: [_],
             drops: %{erasures: erasures}
           } = ctx.info

    assert [%{type: "alloc::string::String", status: :modelled, implementation_verified: false}] =
             Map.values(erasures)

    report = %{
      "trait_impls" => [
        %{
          "def_id" => ctx.info.impl,
          "impl_trait_def_id" => ctx.info.trait,
          "impl_trait_is_builtin" => true,
          "impl_trait_rust_name" => "rustler::types::Encoder",
          "rust_name" => "rustler::types::Encoder<String>",
          "lean_name" => "StringEncoder"
        }
      ],
      "trait_decls" => [],
      "functions" => []
    }

    assert %{"modelled" => true, "label" => label} = VTables.link!(ctx.audited, report)
    assert label =~ "approved String encoding model"
    [method] = ctx.info.methods

    assert_raise ArgumentError, fn ->
      VTables.link!(ctx.audited, %{
        report
        | "functions" => [%{"def_id" => method, "is_opaque" => true}]
      })
    end
  end

  test "rejects opaque tables, altered methods and wrong cleanup", ctx do
    [_, ty] = Lynx.Rust.CallModels.expand(ctx.global["value"], ctx.refs)

    assert_raise ArgumentError, fn ->
      VTables.audit!(
        [%{ctx.global | "value" => [%{"Opaque" => "missing"}, ty]}],
        [],
        ctx.translated,
        ctx.refs
      )
    end

    [method] = ctx.info.methods
    [drop, slot] = ctx.info.shims
    [destructor] = Map.keys(ctx.info.drops.erasures)

    for {id, update} <- [
          {method, fn f -> %{f | "body" => %{}} end},
          {slot, fn f -> put_in(f, ["signature", "abi"], "C") end},
          {drop, fn f -> put_in(f, ["signature", "is_unsafe"], false) end},
          {destructor, fn f -> put_in(f, ["src", "TraitImpl", "item_id"], 1) end}
        ] do
      t =
        update_in(ctx.translated, ["fun_decls"], fn fs ->
          Enum.map(fs, fn f -> if f && f["def_id"] == id, do: update.(f), else: f end)
        end)

      assert_raise ArgumentError, fn -> VTables.audit!([ctx.global], [], t, ctx.refs) end
    end
  end

  test "the LLBC pipeline rejects duplicate foreign table identities", ctx do
    document =
      put_in(ctx.document, ["translated", "global_decls"], [
        ctx.global | ctx.translated["global_decls"]
      ])

    assert_raise ArgumentError, ~r/duplicate LLBC constant identity/, fn ->
      LLBC.audit!(document, ~w(experiment_nif experiment_analysis experiment_core),
        external_calls: [:rustler_encoders]
      )
    end
  end
end
