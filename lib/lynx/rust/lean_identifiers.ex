defmodule Lynx.Rust.LeanIdentifiers do
  @moduledoc false

  # Rewrite generated references, preserving literals, quoted names and nested
  # comments. The caller rejects ambiguous application namespaces.
  def replace(source, names, target) do
    {parts, count} = code(source, names, target, nil, [], 0)
    {parts |> Enum.reverse() |> IO.iodata_to_binary(), count}
  end

  defp code("", _, _, _, acc, count), do: {acc, count}

  defp code("--" <> rest, names, target, _, acc, count) do
    {line, tail} =
      case :binary.match(rest, "\n") do
        :nomatch ->
          {rest, ""}

        {offset, 1} ->
          {binary_part(rest, 0, offset + 1),
           binary_part(rest, offset + 1, byte_size(rest) - offset - 1)}
      end

    code(tail, names, target, nil, [["--", line] | acc], count)
  end

  defp code("/-" <> rest, names, target, _, acc, count) do
    {comment, tail} = comment(rest, 1, ["/-"])
    code(tail, names, target, nil, [comment | acc], count)
  end

  defp code("\"" <> rest, names, target, _, acc, count) do
    {literal, tail} = quoted(rest, ["\""])
    code(tail, names, target, nil, [literal | acc], count)
  end

  defp code("«" <> rest, names, target, _, acc, count) do
    case :binary.match(rest, "»") do
      {offset, size} ->
        name = binary_part(rest, 0, offset + size)
        tail = binary_part(rest, offset + size, byte_size(rest) - offset - size)
        code(tail, names, target, nil, [["«", name] | acc], count)

      :nomatch ->
        raise ArgumentError, "unterminated generated Lean quoted identifier"
    end
  end

  defp code("'\\" <> <<char::utf8, "'", rest::binary>>, names, target, _, acc, count),
    do: code(rest, names, target, nil, [["'\\", <<char::utf8>>, "'"] | acc], count)

  defp code("'" <> <<char::utf8, "'", rest::binary>>, names, target, _, acc, count),
    do: code(rest, names, target, nil, [["'", <<char::utf8>>, "'"] | acc], count)

  defp code(source, names, target, previous, acc, count) do
    raw = Regex.run(~r/^r(\#*)"/, source)

    if raw do
      [opening, hashes] = raw
      rest = binary_part(source, byte_size(opening), byte_size(source) - byte_size(opening))
      closing = "\"" <> hashes

      case :binary.match(rest, closing) do
        {offset, size} ->
          literal = binary_part(rest, 0, offset + size)
          tail = binary_part(rest, offset + size, byte_size(rest) - offset - size)
          code(tail, names, target, nil, [[opening, literal] | acc], count)

        :nomatch ->
          raise ArgumentError, "unterminated generated Lean raw string"
      end
    else
      name =
        Enum.find(names, fn name ->
          String.starts_with?(source, name) and not identifier?(previous) and
            not identifier?(
              source
              |> binary_part(byte_size(name), byte_size(source) - byte_size(name))
              |> String.first()
            )
        end)

      if name do
        rest = binary_part(source, byte_size(name), byte_size(source) - byte_size(name))
        code(rest, names, target, String.last(target), [target | acc], count + 1)
      else
        <<char::utf8, rest::binary>> = source
        code(rest, names, target, <<char::utf8>>, [<<char::utf8>> | acc], count)
      end
    end
  end

  defp identifier?(nil), do: false
  defp identifier?(char), do: Regex.match?(~r/[\p{L}\p{N}\p{M}\p{Pc}\p{Cf}_'.]/u, char)

  defp quoted("\\" <> <<char::utf8, rest::binary>>, acc),
    do: quoted(rest, [["\\", <<char::utf8>>] | acc])

  defp quoted("\"" <> rest, acc), do: {Enum.reverse(["\"" | acc]), rest}
  defp quoted(<<char::utf8, rest::binary>>, acc), do: quoted(rest, [<<char::utf8>> | acc])
  defp quoted("", _), do: raise(ArgumentError, "unterminated generated Lean string")

  defp comment("/-" <> rest, depth, acc), do: comment(rest, depth + 1, ["/-" | acc])
  defp comment("-/" <> rest, 1, acc), do: {Enum.reverse(["-/" | acc]), rest}
  defp comment("-/" <> rest, depth, acc), do: comment(rest, depth - 1, ["-/" | acc])

  defp comment(<<char::utf8, rest::binary>>, depth, acc),
    do: comment(rest, depth, [<<char::utf8>> | acc])

  defp comment("", _, _), do: raise(ArgumentError, "unterminated generated Lean comment")
end
