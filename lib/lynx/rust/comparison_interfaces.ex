defmodule Lynx.Rust.ComparisonInterfaces do
  @moduledoc false
  alias Lynx.Rust.{LLBCJson, ResourceModels}

  @fields %{
    "Eq" => [],
    "Ord" => ~w(cmp max min clamp),
    "PartialOrd" => ~w(partial_cmp lt le gt ge)
  }

  # The pinned Lean library implements these prefix fields. Newer Rust adds
  # helper methods which the collection models never observe. Preserve every
  # executable body and reject an observed helper before narrowing its interface.
  def project!(document, audit) do
    if audit.ordered_collections.families == [] do
      {document, nil}
    else
      document =
        document
        |> LLBCJson.restore_type_references!(document)
        |> LLBCJson.restore_trait_references!(document)
        |> LLBCJson.restore_constant_references!(document)
        |> LLBCJson.restore_spans!(document)

      t = document["translated"]

      traits =
        for d <- t["trait_decls"],
            d,
            name = comparison_name(d),
            name,
            into: %{},
            do: {d["def_id"], @fields[name]}

      for d <- t["trait_decls"], d, fields = traits[d["def_id"]] do
        methods = Enum.take(d["methods"], length(fields))

        unless d["src"] == "Normal" and d["is_unsafe"] == false and
                 Enum.map(methods, & &1["skip_binder"]["name"]) == fields and
                 Enum.all?(Enum.with_index(methods), fn {m, i} ->
                   m["kind"] == %{"TraitMethod" => [d["def_id"], i]}
                 end),
               do: raise(ArgumentError, "inconsistent standard comparison interface")
      end

      removed =
        for f <- t["fun_decls"],
            f,
            source = source(f),
            fields = traits[source["trait_ref"]["id"]],
            fields != nil,
            source["item_id"] >= length(fields),
            into: MapSet.new() do
          unless hd(f["item_meta"]["name"]) == %{"Ident" => ["core", 0]} and f["body"] == "Opaque",
            do: raise(ArgumentError, "cannot omit an executable or first-party comparison helper")

          f["def_id"]
        end

      original =
        Map.new(audit.functions, fn f ->
          d = Enum.find(t["fun_decls"], &(&1 && &1["def_id"] == f["def_id"]))
          {f["def_id"], Map.take(d, ~w(body signature))}
        end)

      t =
        t
        |> Map.update!(
          "fun_decls",
          &Enum.map(&1, fn f -> if f && MapSet.member?(removed, f["def_id"]), do: nil, else: f end)
        )
        |> Map.update!(
          "trait_decls",
          &Enum.map(&1, fn d -> trim(d, traits, fn x -> x["def_id"] end) end)
        )
        |> Map.update!(
          "trait_impls",
          &Enum.map(&1, fn d -> trim(d, traits, fn x -> x["impl_trait"]["id"] end) end)
        )
        |> Map.update!("assoc_item_names", fn rows ->
          Enum.with_index(rows)
          |> Enum.map(fn {row, id} ->
            if fields = traits[id], do: %{row | "methods" => fields}, else: row
          end)
        end)
        |> Map.update!("ordered_decls", fn groups ->
          Enum.flat_map(groups, &retain(&1, removed))
        end)

      refs = ResourceModels.trait_references(t)

      for key <- ~w(fun_decls type_decls trait_decls trait_impls global_decls),
          d <- t[key],
          d,
          do: observed!(d, traits, removed, refs)

      for {id, before} <- original do
        after_f = Enum.find(t["fun_decls"], &(&1 && &1["def_id"] == id))

        unless after_f && Map.take(after_f, ~w(body signature)) == before,
          do:
            raise(
              ArgumentError,
              "comparison interface projection changed an audited implementation"
            )
      end

      {%{document | "translated" => t}, %{traits: Map.keys(traits), omitted: Enum.sort(removed)}}
    end
  end

  defp trim(nil, _, _), do: nil

  defp trim(d, traits, id) do
    if fields = traits[id.(d)],
      do: %{d | "methods" => Enum.take(d["methods"], length(fields))},
      else: d
  end

  defp comparison_name(%{
         "item_meta" => %{
           "name" => [
             %{"Ident" => ["core", 0]},
             %{"Ident" => ["cmp", 0]},
             %{"Ident" => [name, 0]}
           ]
         }
       })
       when is_map_key(@fields, name), do: name

  defp comparison_name(_), do: nil
  defp source(%{"src" => s}) when is_map(s), do: s["TraitImpl"] || s["TraitDefault"]
  defp source(_), do: nil

  defp retain(%{"Fun" => %{"NonRec" => id}} = group, removed),
    do: if(MapSet.member?(removed, id), do: [], else: [group])

  defp retain(%{"Fun" => %{"Rec" => ids}}, removed) do
    case Enum.reject(ids, &MapSet.member?(removed, &1)) do
      [] -> []
      kept -> [%{"Fun" => %{"Rec" => kept}}]
    end
  end

  defp retain(group, _), do: [group]

  defp observed!(
         %{"kind" => %{"TraitMethod" => [_, _]}, "skip_binder" => binding} = method,
         t,
         r,
         refs
       ) do
    ids = [
      binding["id"],
      case binding["default"] do
        %{"id" => id} -> id
        id when is_integer(id) -> id
        _ -> nil
      end
    ]

    if Enum.any?(ids, &(is_integer(&1) and MapSet.member?(r, &1))),
      do: raise(ArgumentError, "observed omitted comparison method binding")

    Enum.each(Map.values(method), &observed!(&1, t, r, refs))
  end

  defp observed!(%{"Fun" => id}, _, removed, _) when is_integer(id) do
    if MapSet.member?(removed, id), do: raise(ArgumentError, "observed omitted comparison helper")
  end

  defp observed!(%{"Trait" => [raw, slot]} = m, traits, removed, refs) do
    d =
      ResourceModels.dictionary(%{"regions" => [], "outlives" => [], "skip_binder" => raw}, refs)

    fields = if d, do: traits[d["trait_decl_ref"]["id"]]

    if fields && slot >= length(fields),
      do: raise(ArgumentError, "observed omitted comparison method")

    Enum.each(Map.values(m), &observed!(&1, traits, removed, refs))
  end

  defp observed!(m, t, r, refs) when is_map(m),
    do: Enum.each(Map.values(m), &observed!(&1, t, r, refs))

  defp observed!(l, t, r, refs) when is_list(l), do: Enum.each(l, &observed!(&1, t, r, refs))
  defp observed!(_, _, _, _), do: :ok
end
