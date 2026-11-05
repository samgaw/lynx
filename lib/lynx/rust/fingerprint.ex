defmodule Lynx.Rust.Fingerprint do
  @moduledoc false

  # Extraction is always rerun. Fingerprints identify the extracted implementation
  # and its build inputs for reuse of kernel-checked proofs, not skipped extraction.
  def extraction!(context, tools, llbc, translation, first_party) do
    model = JSON.decode!(File.read!(llbc))

    files =
      for file <- model["translated"]["files"], file["crate_name"] in first_party do
        case file["name"] do
          %{"Local" => path} ->
            Path.expand(path, context.record["directory"])

          other ->
            raise ArgumentError, "unsupported first-party source identity: #{inspect(other)}"
        end
      end

    manifests =
      context.workspace.crates
      |> Enum.filter(&(&1.id in closure(context.package.id, context.workspace.crates)))
      |> Enum.map(& &1.manifest)

    inputs =
      Enum.uniq(
        files ++
          manifests ++
          [
            Path.join(context.workspace.root, "Cargo.toml"),
            Path.join(context.workspace.root, "Cargo.lock")
          ]
      )

    source_hashes = for path <- Enum.sort(inputs), do: {path, file!(path)}

    tool_hashes =
      for tool <- ~w(charon charon-driver aeneas), do: {tool, file!(Path.join(tools, tool))}

    extern_hashes = for path <- extern_paths(context.record["arguments"]), do: {path, file!(path)}
    record = context.record

    environment =
      Map.merge(
        context.baseline,
        Map.new(record["environment"], fn {key, value} -> {key, digest(value)} end)
      )
      |> Map.drop(record["removed_environment"])

    digest(
      :erlang.term_to_binary(
        {"lynx-rust-1", context.toolchain, record["compiler"], record["directory"],
         record["arguments"], environment, source_hashes, extern_hashes, tool_hashes,
         File.read!(llbc), translation},
        [:deterministic]
      )
    )
  end

  def file!(path), do: path |> File.read!() |> digest()
  def digest(bytes), do: :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)

  defp closure(id, crates) do
    crate = Enum.find(crates, &(&1.id == id))
    [id | Enum.flat_map(crate.dependencies, &closure(&1, crates))] |> Enum.uniq()
  end

  defp extern_paths([]), do: []
  defp extern_paths(["--extern", value | rest]), do: extern_path(value) ++ extern_paths(rest)
  defp extern_paths(["--extern=" <> value | rest]), do: extern_path(value) ++ extern_paths(rest)
  defp extern_paths([_ | rest]), do: extern_paths(rest)

  defp extern_path(value) do
    case String.split(value, "=", parts: 2) do
      [_name, path] -> [path]
      _ -> raise ArgumentError, "Rust extraction requires resolved --extern artifact paths"
    end
  end
end
