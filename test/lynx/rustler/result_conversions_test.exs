defmodule Lynx.Rustler.ResultConversionsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC}
  alias Lynx.Rustler.ResultConversions
  @snapshot Path.expand("../../fixtures/rustler/tagged_decoder_models.json", __DIR__)

  setup do
    document = JSON.decode!(File.read!(@snapshot))
    translated = document["translated"]
    functions = Enum.reject(translated["fun_decls"], &is_nil/1)
    refs = LLBC.type_references!(document)
    models = CallModels.resolve(functions, translated, refs, [:rustler_decoders])
    conversions = Map.filter(models, fn {_, m} -> m[:rustler_result_conversion] end)
    %{functions: functions, translated: translated, refs: refs, models: conversions}
  end

  test "compiled conversions retain the SDK Error specialization and cleanup model", ctx do
    assert Enum.sort(Enum.map(ctx.models, fn {_, m} -> m.rustler_result_conversion end)) == [
             "ok",
             "ok_or"
           ]

    assert :ok = ResultConversions.audit(ctx.functions, ctx.models, ctx.translated, ctx.refs)

    for {_, model} <- ctx.models do
      assert model.keep_params == [true, false]

      for changed <- [
            put_in(model.function, ["signature", "abi"], "C"),
            put_in(model.function, ["signature", "is_unsafe"], true),
            put_in(model.function, ["signature", "output"], %{"Scalar" => "Bool"}),
            put_in(model.function, ["generics", "trait_clauses"], [])
          ] do
        assert ResultConversions.resolve(changed, ctx.translated, ctx.refs) == nil
      end
    end
  end

  test "rejects mismatched error specialization and unrecognized destructor dictionaries", ctx do
    for {_, model} <- ctx.models do
      for changed <- [
            %{model | rustler_error_type: -1},
            %{model | conversion_destruct_trait: -1},
            %{model | conversion_destruct_variables: []}
          ] do
        models = Map.put(ctx.models, model.definition_id, changed)

        assert {:error, _, message} =
                 ResultConversions.audit(ctx.functions, models, ctx.translated, ctx.refs)

        assert message =~ "actual Rustler Error type"
      end
    end

    translated =
      update_in(ctx.translated, ["trait_impls"], fn rows ->
        Enum.map(rows, fn
          %{"src" => "Destruct"} = row -> %{row | "src" => "Normal"}
          row -> row
        end)
      end)

    assert {:error, _, _} =
             ResultConversions.audit(ctx.functions, ctx.models, translated, ctx.refs)
  end
end
