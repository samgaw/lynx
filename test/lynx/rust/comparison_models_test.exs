defmodule Lynx.Rust.ComparisonModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, ComparisonModels, LibraryHelpers, LLBC}
  @snapshot Path.expand("../../fixtures/rustler/comparison.json", __DIR__)

  setup do
    document = @snapshot |> File.read!() |> JSON.decode!()
    t = document["translated"]
    refs = LLBC.type_references!(document)
    models = CallModels.resolve(Enum.reject(t["fun_decls"], &is_nil/1), t, refs, [])
    caller = Enum.at(t["fun_decls"], 20)
    helper = Enum.at(t["fun_decls"], 23)
    %{document: document, t: t, refs: refs, models: models, caller: caller, helper: helper}
  end

  test "audits actual prefix bodies and both concrete scalar methods", ctx do
    assert LibraryHelpers.selected?(ctx.helper, ctx.t)
    assert %{comparison_family: :shared, implementation_verified: false} = ctx.models[25]
    assert %{comparison_family: :default, status: :modelled} = ctx.models[26]
    assert %{comparison_family: :scalar} = ctx.models[28]

    assert {:ok, %{20 => [27, 28]}} =
             ComparisonModels.audit([ctx.caller, ctx.helper], ctx.models, ctx.t, ctx.refs)

    assert %{library_helpers: [23], trait_dependencies: deps} =
             LLBC.audit!(ctx.document, ~w(text_core text_analysis))

    assert 36 in deps[23]
    assert 26 in deps[23]
  end

  test "does not infer a missing ne implementation", ctx do
    for models <- [Map.delete(ctx.models, 27), Map.delete(ctx.models, 28)] do
      assert {:error, _, message} =
               ComparisonModels.audit([ctx.caller, ctx.helper], models, ctx.t, ctx.refs)

      assert message =~ "captured eq/ne"
    end

    t =
      update_in(ctx.t, ["trait_impls"], fn rows ->
        List.update_at(rows, 6, &put_in(&1, ["methods"], [hd(&1["methods"]), nil]))
      end)

    assert {:error, _, _} =
             ComparisonModels.audit([ctx.caller, ctx.helper], ctx.models, t, ctx.refs)
  end

  test "checks comparison method signature, identity and selected default", ctx do
    for change <- [
          put_in(ctx.models[25].function, ["signature", "is_unsafe"], true),
          put_in(ctx.models[25].function, ["signature", "output"], %{
            "Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}
          }),
          put_in(ctx.models[25].function, ["src", "TraitImpl", "reuses_default"], true),
          put_in(ctx.models[25].function, ["src", "TraitImpl", "trait_ref", "id"], 999)
        ] do
      refute ComparisonModels.resolve(change, ctx.t, ctx.refs)
    end

    t =
      update_in(ctx.t, ["trait_decls"], fn rows ->
        List.update_at(rows, 5, fn trait ->
          update_in(
            trait,
            ["methods"],
            &List.update_at(&1, 1, fn method ->
              put_in(method, ["skip_binder", "default", "id"], 27)
            end)
          )
        end)
      end)

    assert {:error, _, _} = ComparisonModels.audit([ctx.helper], ctx.models, t, ctx.refs)
  end

  test "checks prefix helper signature and generic bound without replacing its body", ctx do
    refute LibraryHelpers.selected?(put_in(ctx.helper, ["signature", "is_unsafe"], true), ctx.t)
    refute LibraryHelpers.selected?(put_in(ctx.helper, ["generics", "trait_clauses"], []), ctx.t)
    refute LibraryHelpers.selected?(put_in(ctx.helper, ["signature", "output"], "Never"), ctx.t)
    assert "core::slice::_::starts_with" in LibraryHelpers.includes(%{sysroot: %{path: "full"}})
    refute "core::slice::_::starts_with" in LibraryHelpers.includes()
  end
end
