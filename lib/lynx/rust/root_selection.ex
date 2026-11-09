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
      Enum.flat_map(Enum.reject(roots, &attribute_root?(&1, local_crates)), &["--start-from", &1])
  end

  def validate!(_document, _roots, nil, _local_crates), do: :ok

  def validate!(document, roots, attribute, local_crates) do
    functions = Enum.reject(document["translated"]["fun_decls"], &is_nil/1)

    for root <- roots, attribute_root?(root, local_crates) do
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
        raise ArgumentError,
              "missing, ambiguous or opaque Rust root #{root} selected by #[#{attribute}]; mark the implementation or an ancestor that calls it"
      end
    end

    :ok
  end

  defp attribute_root?(root, local_crates) do
    Regex.match?(@path, root) and
      hd(String.split(root, "::")) in ["crate" | local_crates]
  end
end
