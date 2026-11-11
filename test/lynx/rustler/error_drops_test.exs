defmodule Lynx.Rustler.ErrorDropsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{DropModels, LLBC}
  alias Lynx.Rustler.ErrorDrops
  @crates ~w(experiment_nif experiment_core experiment_analysis)
  @snapshot Path.expand("../../fixtures/rustler/error_drop.json", __DIR__)

  setup do
    %{"document" => document, "layout" => layout} = JSON.decode!(File.read!(@snapshot))
    %{document: document, layout: layout}
  end

  test "retains explicit partial destruction and links exact compiler glue", ctx do
    {document, proof} = ErrorDrops.lower!(ctx.document, ctx.layout, @crates)
    assert Enum.any?(proof.sites, &(&1.mode == :error))
    assert Enum.any?(proof.sites, &(&1.mode == :result))
    models = ErrorDrops.models!(document, proof)
    assert map_size(models) == 2

    for {_, model} <- models do
      assert %{implementation_verified: false, can_fail: true, status: :modelled} = model
      assert model.label =~ "boxed errors exhaust"
    end

    assert Enum.any?(Map.values(models), &(&1.lean == "Lynx.Rustler.Decoding.dropDecoderError"))
    assert Enum.any?(Map.values(models), &(&1.lean == "Lynx.Rustler.Decoding.dropErrResult"))
    assert document["translated"]["type_decls"] == ctx.document["translated"]["type_decls"]
    {_, declaration} = Enum.at(proof.declarations, 0)
    id = declaration["def_id"]
    changed = put_in(document, ["translated", "fun_decls", Access.at(id), "body"], %{})

    assert_raise ArgumentError, ~r/inconsistent validated Rustler error drop/, fn ->
      ErrorDrops.models!(changed, proof)
    end
  end

  test "requires compiler-generated Result destruction metadata", ctx do
    functions = ctx.document["translated"]["fun_decls"]

    glue =
      Enum.find(
        functions,
        &(&1 && DropModels.generated?(&1) && length(&1["generics"]["types"]) == 2)
      )

    for changed <- [
          Map.put(glue, "body", "Opaque"),
          put_in(glue, ["signature", "is_unsafe"], false),
          put_in(glue, ["signature", "abi"], "C"),
          put_in(glue, ["src", "TraitImpl", "reuses_default"], true)
        ] do
      document =
        put_in(ctx.document, ["translated", "fun_decls", Access.at(glue["def_id"])], changed)

      assert_raise ArgumentError, ~r/Result drop/, fn ->
        ErrorDrops.lower!(document, ctx.layout, @crates)
      end
    end
  end

  test "ordinary erasure still rejects Rustler errors with boxed payloads", ctx do
    function =
      Enum.find(
        ctx.document["translated"]["fun_decls"],
        &(&1 &&
            Enum.any?(&1["item_meta"]["name"], fn n ->
              n == %{"Ident" => ["try_decode_field", 0]}
            end))
      )

    assert {:error, _, message} =
             DropModels.audit(
               [function],
               [],
               ctx.document["translated"],
               LLBC.type_references!(ctx.document),
               @crates
             )

    assert message =~ "concrete destruction-free payloads"
  end

  test "does not simplify cleanup across a replacement of the matched result", ctx do
    {_, ordinary} = ErrorDrops.lower!(ctx.document, ctx.layout, @crates)
    assert Enum.any?(ordinary.sites, &(&1.mode == :error))
    # A call writing the result local invalidates the enclosing discriminant.
    changed = inject_tag_write(ctx.document)
    refute changed == ctx.document
    {_, proof} = ErrorDrops.lower!(changed, ctx.layout, @crates)
    # The cleanup still has an explicit switch and a partial Result drop.
    assert Enum.any?(proof.sites, &(&1.mode == :result))

    assert cleanup_switches(elem(ErrorDrops.lower!(changed, ctx.layout, @crates), 0)) >
             cleanup_switches(elem(ErrorDrops.lower!(ctx.document, ctx.layout, @crates), 0))
  end

  defp inject_tag_write(%{"statements" => statements} = block) do
    statements =
      Enum.flat_map(statements, fn statement ->
        case statement do
          %{
            "kind" => %{
              "Switch" => %{
                "data" => %{
                  "scrutinee" => %{"Discriminant" => %{"kind" => %{"Local" => 3}}},
                  "fallback" => 1
                }
              }
            }
          } ->
            [%{"kind" => %{"Call" => %{"dest" => %{"kind" => %{"Local" => 3}}}}}, statement]

          other ->
            [inject_tag_write(other)]
        end
      end)

    %{block | "statements" => statements}
  end

  defp inject_tag_write(map) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, inject_tag_write(v)} end)

  defp inject_tag_write(list) when is_list(list), do: Enum.map(list, &inject_tag_write/1)
  defp inject_tag_write(value), do: value

  defp cleanup_switches(%{
         "scrutinee" => %{"Discriminant" => %{"kind" => %{"Local" => 3}}},
         "fallback" => 1
       }),
       do: 1

  defp cleanup_switches(map) when is_map(map),
    do: Enum.sum(Enum.map(Map.values(map), &cleanup_switches/1))

  defp cleanup_switches(list) when is_list(list),
    do: Enum.sum(Enum.map(list, &cleanup_switches/1))

  defp cleanup_switches(_), do: 0

  test "rejects SDK identity collisions, layouts and first-party substitution", ctx do
    {_, proof} = ErrorDrops.lower!(ctx.document, ctx.layout, @crates)
    {_, declaration} = Enum.at(proof.declarations, 0)
    document = update_in(ctx.document, ["translated", "fun_decls"], &(&1 ++ [declaration]))

    assert_raise ArgumentError, ~r/identity collision/, fn ->
      ErrorDrops.lower!(document, ctx.layout, @crates)
    end

    assert_raise ArgumentError, ~r/first-party Rustler/, fn ->
      ErrorDrops.lower!(ctx.document, ctx.layout, ["rustler" | @crates])
    end
  end
end
