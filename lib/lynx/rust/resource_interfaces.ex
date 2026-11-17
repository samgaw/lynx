defmodule Lynx.Rust.ResourceInterfaces do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, LLBCJson, ResourceAudit, ResourceModels}
  @trait ~w(rustler resource traits Resource)
  @types [
    ~w(rustler env Env),
    ~w(rustler types local_pid LocalPid),
    ~w(rustler resource monitor Monitor)
  ]

  # Full-MIR discovery materializes unused foreign callback defaults. Never
  # manufacture implementations for their opaque FFI types: validate defaults,
  # omit only an unobserved interface, and preserve every audited body/signature.
  def project!(document, audit) do
    if Enum.any?(audit.external_calls, fn {_, m} -> m[:native_resource_type] != nil end) do
      project_resource!(document, audit)
    else
      {document, nil}
    end
  end

  defp project_resource!(document, audit) do
    document =
      document
      |> LLBCJson.restore_type_references!(document)
      |> LLBCJson.restore_trait_references!(document)
      |> LLBCJson.restore_constant_references!(document)
      |> LLBCJson.restore_spans!(document)

    t = document["translated"]

    case Enum.find(t["trait_decls"], &(&1 && &1["item_meta"]["name"] == path(@trait))) do
      nil -> {document, nil}
      trait -> project_defaults!(document, audit, trait)
    end
  end

  defp project_defaults!(document, audit, trait) do
    t = document["translated"]
    impls = Enum.filter(t["trait_impls"], &(&1 && &1["impl_trait"]["id"] == trait["def_id"]))

    if Enum.all?(impls, &Enum.all?(&1["methods"], fn m -> is_nil(m) end)) do
      {document, nil}
    else
      refs = LLBC.type_references!(t)
      dictionaries = ResourceModels.trait_references(t)

      for impl <- impls do
        [payload] = CallModels.expand(impl["impl_trait"]["generics"]["types"], refs)

        %{"generics" => %{"trait_refs" => [dictionary]}} = hd(impl["consts"])

        unless ResourceAudit.payload?(
                 payload,
                 dictionary,
                 trait["def_id"],
                 t,
                 refs,
                 dictionaries
               ),
               do:
                 raise(
                   ArgumentError,
                   "cannot omit a nondefault or unsupported Rustler resource callback interface"
                 )
      end

      trait_id = trait["def_id"]

      removed =
        for f <- t["fun_decls"],
            f,
            match?(
              %{"TraitDefault" => %{"trait_ref" => %{"id" => ^trait_id}}},
              f["src"]
            ),
            into: MapSet.new() do
          unless f["body"] == "Opaque" and f["item_meta"]["is_local"] == false and
                   f["item_meta"]["name"] in Enum.map(~w(destructor down), &path(@trait ++ [&1])),
                 do:
                   raise(
                     ArgumentError,
                     "cannot omit an executable or first-party resource callback"
                   )

          f["def_id"]
        end

      types =
        for d <- t["type_decls"],
            d,
            d["item_meta"]["name"] in Enum.map(@types, &path/1),
            into: MapSet.new() do
          unless d["kind"] == "Opaque" and d["item_meta"]["is_local"] == false,
            do: raise(ArgumentError, "cannot omit an executable resource callback type")

          d["def_id"]
        end

      before =
        Map.new(audit.functions, fn f ->
          d = Enum.find(t["fun_decls"], &(&1 && &1["def_id"] == f["def_id"]))
          {f["def_id"], Map.take(d, ~w(body signature))}
        end)

      projected =
        t
        |> Map.update!(
          "fun_decls",
          &Enum.map(&1, fn f -> if f && MapSet.member?(removed, f["def_id"]), do: nil, else: f end)
        )
        |> Map.update!(
          "type_decls",
          &Enum.map(&1, fn d -> if d && MapSet.member?(types, d["def_id"]), do: nil, else: d end)
        )
        |> Map.update!(
          "trait_decls",
          &Enum.map(&1, fn d ->
            if d && d["def_id"] == trait["def_id"], do: %{d | "methods" => []}, else: d
          end)
        )
        |> Map.update!(
          "trait_impls",
          &Enum.map(&1, fn d ->
            if d && d["impl_trait"]["id"] == trait["def_id"], do: %{d | "methods" => []}, else: d
          end)
        )
        |> Map.update!("assoc_item_names", fn rows ->
          Enum.with_index(rows)
          |> Enum.map(fn {row, id} ->
            if id == trait["def_id"], do: %{row | "methods" => []}, else: row
          end)
        end)
        |> Map.update!(
          "ordered_decls",
          &Enum.flat_map(&1, fn group -> retain(group, removed, types) end)
        )

      # Env and PID types can also belong to separately admitted codecs. Keep
      # any such type referenced outside the omitted callback interface.
      used =
        Enum.reduce(
          ~w(fun_decls type_decls trait_decls trait_impls global_decls),
          MapSet.new(),
          fn key, ids ->
            type_ids(projected[key], ids)
          end
        )

      types = MapSet.difference(types, used)

      projected =
        projected
        |> Map.put(
          "type_decls",
          Enum.map(t["type_decls"], fn d ->
            if d && MapSet.member?(types, d["def_id"]), do: nil, else: d
          end)
        )
        |> Map.put(
          "ordered_decls",
          Enum.flat_map(t["ordered_decls"], &retain(&1, removed, types))
        )

      for key <- ~w(fun_decls type_decls trait_decls trait_impls global_decls),
          d <- projected[key],
          d,
          do: observed!(d, trait["def_id"], removed, types, dictionaries)

      for {id, previous} <- before do
        f = Enum.find(projected["fun_decls"], &(&1 && &1["def_id"] == id))

        unless f && Map.take(f, ~w(body signature)) == previous,
          do:
            raise(
              ArgumentError,
              "resource interface projection changed an audited implementation"
            )
      end

      {%{document | "translated" => projected},
       %{
         trait: trait["def_id"],
         omitted_functions: Enum.sort(removed),
         omitted_types: Enum.sort(types)
       }}
    end
  end

  defp type_ids(%{"Adt" => %{"id" => id, "builtin" => nil}} = m, ids),
    do: type_ids(Map.values(m), MapSet.put(ids, id))

  defp type_ids(m, ids) when is_map(m), do: type_ids(Map.values(m), ids)
  defp type_ids(l, ids) when is_list(l), do: Enum.reduce(l, ids, &type_ids/2)
  defp type_ids(_, ids), do: ids

  defp retain(group, removed, types) do
    case Map.to_list(group) do
      [{kind, %{"NonRec" => id}}] when kind in ["Fun", "Type"] ->
        omitted = if kind == "Fun", do: removed, else: types
        if MapSet.member?(omitted, id), do: [], else: [group]

      [{kind, %{"Rec" => ids}}] when kind in ["Fun", "Type"] ->
        omitted = if kind == "Fun", do: removed, else: types

        case Enum.reject(ids, &MapSet.member?(omitted, &1)) do
          [] -> []
          kept -> [%{kind => %{"Rec" => kept}}]
        end

      _ ->
        [group]
    end
  end

  defp observed!(%{"Adt" => %{"id" => id, "builtin" => nil}} = m, trait, functions, types, refs) do
    if MapSet.member?(types, id),
      do: raise(ArgumentError, "observed omitted resource callback type")

    Enum.each(Map.values(m), &observed!(&1, trait, functions, types, refs))
  end

  defp observed!(%{"Fun" => id}, _, functions, _, _) when is_integer(id) do
    if MapSet.member?(functions, id),
      do: raise(ArgumentError, "observed omitted resource callback")
  end

  defp observed!(%{"Trait" => [raw, _]} = m, trait, functions, types, refs) do
    d =
      ResourceModels.dictionary(%{"regions" => [], "outlives" => [], "skip_binder" => raw}, refs)

    if d && d["trait_decl_ref"]["id"] == trait,
      do: raise(ArgumentError, "observed omitted resource callback method")

    Enum.each(Map.values(m), &observed!(&1, trait, functions, types, refs))
  end

  defp observed!(
         %{"kind" => %{"TraitMethod" => _}, "skip_binder" => binding} = m,
         trait,
         functions,
         types,
         refs
       ) do
    if Enum.any?(
         [binding["id"], get_in(binding, ["default", "id"])],
         &MapSet.member?(functions, &1)
       ),
       do: raise(ArgumentError, "observed omitted resource callback binding")

    Enum.each(Map.values(m), &observed!(&1, trait, functions, types, refs))
  end

  defp observed!(m, trait, functions, types, refs) when is_map(m),
    do: Enum.each(Map.values(m), &observed!(&1, trait, functions, types, refs))

  defp observed!(l, trait, functions, types, refs) when is_list(l),
    do: Enum.each(l, &observed!(&1, trait, functions, types, refs))

  defp observed!(_, _, _, _, _), do: :ok
  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})
end
