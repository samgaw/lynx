defmodule Lynx.Rust.SlicePatternsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LibraryHelpers, LLBC, LLBCJson, SlicePatterns}
  @snapshot Path.expand("../../fixtures/rustler/slice_pattern.json", __DIR__)

  setup do
    doc = @snapshot |> File.read!() |> JSON.decode!()
    t = doc["translated"]
    helpers = Enum.filter(t["fun_decls"], &(&1 && LibraryHelpers.selected?(&1, t)))

    strip =
      Enum.find(
        helpers,
        &(List.last(&1["item_meta"]["name"]) == %{"Ident" => ["strip_prefix", 0]})
      )

    methods = Enum.reject(helpers, &(&1 == strip))
    %{document: doc, t: t, strip: strip, methods: methods}
  end

  test "links actual slice and array pattern bodies and the indirect method call", ctx do
    assert %{library_helpers: ids, trait_dependencies: deps} =
             LLBC.audit!(ctx.document, ~w(prefix_core prefix_analysis))

    assert MapSet.new(ids) ==
             MapSet.new([ctx.strip["def_id"] | Enum.map(ctx.methods, & &1["def_id"])])

    for method <- ctx.methods do
      assert Enum.any?(deps, fn {_, selected} -> method["def_id"] in selected end)
      assert %{"Structured" => _} = method["body"]
    end
  end

  test "rejects missing or opaque pattern conversions", ctx do
    for method <- ctx.methods do
      changed =
        put_in(
          ctx.document,
          ["translated", "fun_decls", Access.at(method["def_id"]), "body"],
          "Opaque"
        )

      assert_raise CompileError, ~r/SlicePattern/, fn ->
        LLBC.audit!(changed, ~w(prefix_core prefix_analysis))
      end
    end
  end

  test "validates safe signatures and nominal trait identity", ctx do
    for method <- ctx.methods do
      refute SlicePatterns.selected?(put_in(method, ["signature", "is_unsafe"], true), ctx.t)

      refute SlicePatterns.selected?(
               put_in(method, ["src", "TraitImpl", "trait_ref", "id"], 99999),
               ctx.t
             )

      refute SlicePatterns.selected?(
               put_in(method, ["signature", "output"], %{"Scalar" => "Bool"}),
               ctx.t
             )
    end

    refute SlicePatterns.selected?(put_in(ctx.strip, ["generics", "trait_clauses"], []), ctx.t)
    refute SlicePatterns.selected?(put_in(ctx.strip, ["signature", "abi"], "C"), ctx.t)
  end

  test "suffix selection retains the same checked pattern interface", ctx do
    suffix =
      put_in(ctx.strip, ["item_meta", "name", Access.at(-1)], %{"Ident" => ["strip_suffix", 0]})

    assert LibraryHelpers.selected?(suffix, ctx.t)
    refute LibraryHelpers.selected?(put_in(suffix, ["signature", "is_unsafe"], true), ctx.t)
    refute LibraryHelpers.selected?(put_in(suffix, ["generics", "trait_clauses"], []), ctx.t)
    refute LibraryHelpers.selected?(Map.put(suffix, "body", "Opaque"), ctx.t)
  end

  test "checks associated item and trait method signature", ctx do
    trait =
      ctx.strip["generics"]["trait_clauses"] |> hd() |> get_in(["trait_", "skip_binder", "id"])

    changed =
      put_in(
        ctx.t,
        [
          "trait_decls",
          Access.at(trait),
          "methods",
          Access.at(0),
          "skip_binder",
          "signature",
          "output"
        ],
        %{"Scalar" => "Bool"}
      )

    refute SlicePatterns.selected?(ctx.strip, changed)
    for method <- ctx.methods, do: refute(SlicePatterns.selected?(method, changed))
  end

  test "constant references in array types never resolve through the type table", ctx do
    document =
      ctx.document
      |> LLBCJson.restore_constant_references!(ctx.document)
      |> deduplicate_array_lengths()

    assert document != ctx.document
    assert %{library_helpers: helpers} = LLBC.audit!(document, ~w(prefix_core prefix_analysis))
    assert ctx.strip["def_id"] in helpers
  end

  test "rejects unsupported first-party constant-generic pattern methods", ctx do
    array = Enum.find(ctx.methods, &(&1["generics"]["const_generics"] != []))
    name = [%{"Ident" => ["prefix_core", 0]}, %{"Ident" => ["custom_pattern", 0]}]

    changed =
      put_in(
        ctx.document,
        ["translated", "fun_decls", Access.at(array["def_id"]), "item_meta", "name"],
        name
      )

    assert_raise CompileError, ~r/unsupported constant-generic first-party SlicePattern/, fn ->
      LLBC.audit!(changed, ~w(prefix_core prefix_analysis))
    end
  end

  defp deduplicate_array_lengths(%{
         "Array" => [
           type,
           %{"Value" => [id, [%{"Integer" => %{"Unsigned" => ["Usize", "4"]}}, _]]},
           proof
         ]
       }),
       do: %{"Array" => [type, %{"Deduplicated" => id}, proof]}

  defp deduplicate_array_lengths(map) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, deduplicate_array_lengths(v)} end)

  defp deduplicate_array_lengths(list) when is_list(list),
    do: Enum.map(list, &deduplicate_array_lengths/1)

  defp deduplicate_array_lengths(value), do: value
end
