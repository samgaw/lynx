defmodule Lynx.Rust.NativeIndexBounds do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # Only the checked standard array wrapper, with its actual usize delegation,
  # a literal length and a literal in-bounds index. Dynamic indexes remain fallible.
  def safe?(call, %{lean: "Aeneas.Std.core.array.Array.index", builtin: true}, %{
        translated: translated,
        references: refs
      }) do
    with %{"Regular" => %{"generics" => generic}} <- call["func"],
         generic <- CallModels.expand(generic, refs),
         %{
           "types" => [element, index, output],
           "const_generics" => [length],
           "trait_refs" => [dictionary]
         } <- generic,
         true <- index == usize() and element == output,
         {:ok, length} <- literal(length, refs),
         [input, %{"Const" => constant}] <- call["args"],
         {:ok, offset} <- literal(constant, refs),
         true <- offset < length,
         %{"Ref" => [_, %{"Array" => [^element, actual, nil]}, "Shared"]} <-
           CallModels.expand(operand_type(input), refs),
         {:ok, ^length} <- literal(actual, refs),
         true <- delegation?(dictionary, element, translated, refs) do
      true
    else
      _ -> false
    end
  end

  def safe?(_, _, _), do: false

  defp operand_type(%{"Move" => place}), do: place["ty"]
  defp operand_type(%{"Copy" => place}), do: place["ty"]
  defp operand_type(_), do: nil

  defp literal(%{"Value" => [_, value]}, refs), do: literal(value, refs)

  defp literal([%{"Integer" => %{"Unsigned" => ["Usize", text]}}, type], refs)
       when is_binary(text) do
    case Integer.parse(text) do
      {value, ""} when value >= 0 and value <= 4_294_967_295 ->
        if CallModels.expand(type, refs) == usize(), do: {:ok, value}, else: :error

      _ ->
        :error
    end
  end

  defp literal(_value, _refs), do: :error

  defp delegation?(
         %{"regions" => [], "outlives" => [], "skip_binder" => dictionary},
         element,
         translated,
         refs
       ) do
    with %{
           "kind" => %{"TraitImpl" => %{"id" => id, "generics" => args}},
           "trait_decl_ref" => outer
         } <- dictionary,
         true <-
           args["types"] == [element, usize(), element] and args["const_generics"] == [] and
             args["regions"] == [],
         [inner] <- args["trait_refs"],
         impl when not is_nil(impl) <-
           Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == id)),
         true <-
           impl["item_meta"]["name"] ==
             path(~w(core slice index)) ++ [%{"Impl" => %{"Trait" => id}}],
         true <-
           impl["src"] == "Normal" and impl["is_negative"] == false and impl["is_unsafe"] == false,
         outer_trait when not is_nil(outer_trait) <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == outer["id"])),
         true <- outer_trait["item_meta"]["name"] == path(~w(core ops index Index)),
         true <- outer["generics"] == arguments([%{"Slice" => [element, nil]}, usize(), element]),
         variables = Enum.map(0..2, &%{"TypeVar" => %{"Free" => &1}}),
         [t, index, output] = variables,
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => outer["id"],
             "generics" => arguments([%{"Slice" => [t, nil]}, index, output])
           },
         %{"regions" => [], "outlives" => [], "skip_binder" => inner} <- inner,
         %{
           "kind" => %{"TraitImpl" => %{"id" => inner_id, "generics" => inner_args}},
           "trait_decl_ref" => decl
         } <- inner,
         true <- inner_args == arguments([element]),
         inner_impl when not is_nil(inner_impl) <-
           Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == inner_id)),
         true <-
           inner_impl["src"] == "Normal" and inner_impl["is_negative"] == false and
             inner_impl["is_unsafe"] == true,
         true <- scalar_index_params?(inner_impl["generics"]),
         true <-
           inner_impl["item_meta"]["name"] ==
             path(~w(core slice index)) ++ [%{"Impl" => %{"Trait" => inner_id}}],
         trait when not is_nil(trait) <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == decl["id"])),
         true <- trait["item_meta"]["name"] == path(~w(core slice index SliceIndex)),
         true <- decl["generics"] == arguments([usize(), %{"Slice" => [element, nil]}, element]),
         type = %{"TypeVar" => %{"Free" => 0}},
         true <-
           CallModels.expand(inner_impl["impl_trait"], refs) == %{
             "id" => decl["id"],
             "generics" => arguments([usize(), %{"Slice" => [type, nil]}, type])
           } do
      true
    else
      _ -> false
    end
  end

  defp delegation?(_, _, _, _), do: false

  defp scalar_index_params?(%{"types" => [%{"index" => 0}]} = params),
    do:
      Enum.all?(
        ~w(regions const_generics trait_clauses trait_type_constraints outlives),
        &(params[&1] == [])
      )

  defp scalar_index_params?(_), do: false

  defp usize, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}

  defp arguments(types),
    do: %{"types" => types, "regions" => [], "const_generics" => [], "trait_refs" => []}

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
