defmodule Lynx.Rust.RootSelection do
  @moduledoc false
  @path ~r/\A[A-Za-z_][A-Za-z_0-9]*(::[A-Za-z_][A-Za-z_0-9]*)+\z/

  def attribute!(nil), do: nil

  def attribute!(attribute) when is_binary(attribute) do
    if Regex.match?(@path, attribute),
      do: attribute,
      else: raise(ArgumentError, "root_attribute must be a qualified Rust attribute path")
  end

  def attribute!(_),
    do: raise(ArgumentError, "root_attribute must be a qualified Rust attribute path")

  def arguments(roots, nil, _local_crates), do: Enum.flat_map(roots, &["--start-from", &1])

  def arguments(roots, attribute, local_crates) do
    attribute!(attribute)

    ["--start-from-attribute=" <> attribute] ++
      Enum.flat_map(Enum.reject(roots, &literal_root?(&1, local_crates)), &["--start-from", &1])
  end

  def validate!(document, roots, attribute, local_crates),
    do: validate!(document, roots, attribute, local_crates, local_crates)

  def validate!(document, roots, attribute, local_crates, workspace_crates) do
    functions = Enum.reject(document["translated"]["fun_decls"], &is_nil/1)

    for root <- roots, literal_root?(root, workspace_crates) do
      expected = String.split(root, "::")

      expected =
        if hd(expected) == "crate",
          do: [document["translated"]["crate_name"] | tl(expected)],
          else: expected

      matches =
        Enum.filter(functions, fn function ->
          parts =
            Enum.map(function["item_meta"]["name"], fn
              %{"Ident" => [name, _]} -> name
              %{"Builtin" => ["Closure", _]} -> "_"
              _ -> nil
            end)

          parts == expected
        end)

      unless match?([%{"body" => body}] when is_map(body), matches) do
        detail =
          if attribute && literal_root?(root, local_crates),
            do:
              "selected by #[#{attribute}]; mark the implementation or an ancestor that calls it",
            else:
              "selected by path; every requested workspace function must have an extracted implementation"

        raise ArgumentError, "missing, ambiguous or opaque Rust root #{root} #{detail}"
      end
    end

    :ok
  end

  # The pinned Aeneas pruning pass seeds its uses from local functions and impls.
  # Treat selected first-party dependency items as local to this extraction.
  # Only the backend input receives this marker. Rust identities and bodies stay
  # intact, and the audit always reads the original compiler metadata.
  def retain_workspace_roots(document, first_party) do
    Enum.reduce(
      [{"fun_decls", "functions"}, {"trait_impls", "trait_impls"}],
      {document, %{}},
      fn {llbc_key, translation_key}, {document, retained} ->
        path = ["translated", llbc_key]

        {items, ids} =
          Enum.map_reduce(get_in(document, path), MapSet.new(), fn
            %{
              "def_id" => id,
              "item_meta" => %{
                "is_local" => false,
                "started_from" => true,
                "opacity" => "Transparent",
                "name" => [%{"Ident" => [crate, _]} | _]
              }
            } = item,
            ids ->
              if crate in first_party,
                do: {put_in(item, ["item_meta", "is_local"], true), MapSet.put(ids, id)},
                else: {item, ids}

            item, ids ->
              {item, ids}
          end)

        if MapSet.size(ids) == 0,
          do: {document, retained},
          else: {put_in(document, path, items), Map.put(retained, translation_key, ids)}
      end
    )
  end

  def restore_workspace_origins(translation, retained) do
    Enum.reduce(retained, translation, fn {key, ids}, translation ->
      Map.update!(translation, key, fn rows ->
        Enum.map(rows, fn row ->
          if MapSet.member?(ids, row["def_id"]),
            do: Map.replace!(row, "is_local", false),
            else: row
        end)
      end)
    end)
  end

  defp literal_root?(root, local_crates) do
    Regex.match?(@path, root) and
      hd(String.split(root, "::")) in ["crate" | local_crates]
  end
end
