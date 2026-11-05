defmodule Lynx.Rust.Workspace do
  @moduledoc false

  # This is discovery only. Membership and dependency order do not establish
  # that any Rust body has been extracted or verified.
  def discover(manifest, cargo_options \\ [], toolchain \\ nil) do
    manifest = Path.expand(manifest)
    args = ["metadata", "--format-version", "1", "--locked", "--manifest-path", manifest]

    {command, args} =
      if toolchain, do: {"rustup", ["run", toolchain, "cargo" | args]}, else: {"cargo", args}

    case System.cmd(command, args ++ cargo_options,
           cd: Path.dirname(manifest),
           stderr_to_stdout: true
         ) do
      {json, 0} -> decode(json)
      {message, status} -> {:error, "cargo metadata failed (#{status}): #{message}"}
    end
  rescue
    error in ErlangError -> {:error, "cannot run cargo metadata: #{Exception.message(error)}"}
  end

  # Cargo permits cycles through dev-dependencies. They are not part of the
  # selected library build and must not create proof-order cycles.
  defp implementation_dependencies(node) do
    Enum.filter(node["deps"], fn dep ->
      Enum.any?(dep["dep_kinds"], &(&1["kind"] != "dev"))
    end)
  end

  defp decode(json) do
    with {:ok, metadata} <- JSON.decode(json),
         %{
           "workspace_root" => root,
           "workspace_members" => members,
           "packages" => packages,
           "resolve" => %{"nodes" => nodes}
         } <- metadata do
      members = MapSet.new(members)
      packages = Map.new(packages, &{&1["id"], &1})
      nodes = Map.new(nodes, &{&1["id"], &1})
      graph = :digraph.new()

      try do
        for id <- members, do: :digraph.add_vertex(graph, id)

        for id <- members,
            dep <- implementation_dependencies(Map.fetch!(nodes, id)),
            MapSet.member?(members, dep["pkg"]) do
          :digraph.add_edge(graph, dep["pkg"], id)
        end

        case :digraph_utils.topsort(graph) do
          false ->
            {:error, "Cargo workspace dependency graph contains a cycle"}

          order ->
            crates =
              Enum.map(order, fn id ->
                package = Map.fetch!(packages, id)

                dependencies =
                  Enum.map(implementation_dependencies(Map.fetch!(nodes, id)), & &1["pkg"])

                %{
                  id: id,
                  name: package["name"],
                  manifest: package["manifest_path"],
                  targets: package["targets"],
                  edition: package["edition"],
                  features: Map.fetch!(nodes, id)["features"],
                  resolved_dependencies: Map.fetch!(nodes, id)["deps"],
                  dependencies: Enum.filter(dependencies, &MapSet.member?(members, &1)),
                  external_dependencies: Enum.reject(dependencies, &MapSet.member?(members, &1))
                }
              end)

            {:ok,
             %{
               root: root,
               crates: crates,
               packages: packages,
               target_directory: metadata["target_directory"]
             }}
        end
      after
        :digraph.delete(graph)
      end
    else
      _ -> {:error, "invalid or incomplete cargo metadata"}
    end
  end
end
