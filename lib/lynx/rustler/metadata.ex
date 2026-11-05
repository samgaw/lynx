defmodule Lynx.Rustler.Metadata do
  @moduledoc false

  @manifest Path.expand("../../../native/rustler_metadata/Cargo.toml", __DIR__)

  # Reading metadata opens the native library and executes its initializers.
  # Call only for the application's just-built Rustler 0.39 artifacts.
  def inspect!(library) do
    ensure_loaded!()

    library = Path.expand(library)
    # Some dynamic loaders retain Rust libraries after dlclose. Cargo reuses
    # paths between feature configurations, so reading that path again can
    # return a previous image. A unique sibling preserves dependency lookup
    # while ensuring we inspect the bytes from this build.
    copy = library <> ".lynx-#{System.pid()}-#{System.unique_integer([:positive])}"
    File.cp!(library, copy)

    {module, exports} =
      try do
        read_exports(copy)
      after
        File.rm!(copy)
      end

    names = Enum.map(exports, fn {name, arity, _flags} -> {name, arity} end)
    if length(names) != MapSet.size(MapSet.new(names)), do: raise("duplicate NIF exports")
    %{module: module, exports: Enum.sort(exports)}
  end

  def bindings!(expanded_file, compiled, only \\ nil) do
    selected = select!(compiled.exports, only)
    ensure_loaded!()
    parser = :persistent_term.get({__MODULE__, :parser})
    selection = Enum.map(selected, fn {name, arity} -> [name, arity] end)

    {output, status} =
      System.cmd(parser, [expanded_file, JSON.encode!(selection)], stderr_to_stdout: true)

    if status != 0, do: raise("cannot discover Rustler bindings in #{expanded_file}:\n#{output}")
    bindings = JSON.decode!(output)

    exports =
      Enum.sort(
        for binding <- bindings, do: {binding["name"], binding["arity"], binding["flags"]}
      )

    if exports != compiled.exports,
      do: raise("expanded Rustler bindings do not match the compiled NIF table")

    %{
      module: compiled.module,
      exports: compiled.exports,
      bindings: Enum.filter(bindings, &({&1["name"], &1["arity"]} in selected))
    }
  end

  defp select!(exports, only) do
    available = Enum.map(exports, fn {name, arity, _flags} -> {name, arity} end)

    selected =
      case only do
        nil ->
          available

        [_ | _] ->
          Enum.map(only, fn
            {name, arity} when is_atom(name) and is_integer(arity) and arity >= 0 ->
              {Atom.to_string(name), arity}

            other ->
              raise ArgumentError, "invalid Rustler binding selection: #{inspect(other)}"
          end)

        _ ->
          raise ArgumentError, "Rustler :only must be a nonempty list of {name, arity} bindings"
      end

    if length(selected) != MapSet.size(MapSet.new(selected)),
      do: raise(ArgumentError, "duplicate Rustler binding selection")

    for binding <- selected,
        binding not in available,
        do: raise(ArgumentError, "selected Rustler binding is not exported: #{inspect(binding)}")

    selected
  end

  defp ensure_loaded! do
    unless {:read_exports, 1} in __MODULE__.module_info(:nifs) do
      :global.trans({__MODULE__, self()}, fn ->
        unless {:read_exports, 1} in __MODULE__.module_info(:nifs), do: build_and_load!()
      end)
    end
  end

  defp build_and_load! do
    case :os.type() do
      {:unix, _} -> :ok
      _ -> raise "Rustler metadata inspection currently supports Unix NIF libraries only"
    end

    {output, status} =
      System.cmd(
        "cargo",
        ["build", "--locked", "--manifest-path", @manifest, "--message-format=json"],
        stderr_to_stdout: true
      )

    if status != 0, do: raise("cannot build Rustler metadata reader:\n" <> output)

    libraries =
      for line <- String.split(output, "\n"),
          {:ok,
           %{
             "reason" => "compiler-artifact",
             "target" => %{"name" => "lynx_rustler_metadata"},
             "filenames" => files
           }} <- [JSON.decode(line)],
          file <- files,
          Path.extname(file) in [".so", ".dylib"],
          do: file

    [library] = libraries

    [parser] =
      for line <- String.split(output, "\n"),
          {:ok,
           %{
             "reason" => "compiler-artifact",
             "target" => %{"name" => "lynx-rustler-bindings"},
             "executable" => parser
           }}
          when is_binary(parser) <- [JSON.decode(line)],
          do: parser

    # Erlang requires .so even on macOS. A unique path avoids replacing a mapped
    # library from another VM during builds.
    directory =
      Path.join(
        System.tmp_dir!(),
        "lynx-metadata-#{System.pid()}-#{System.unique_integer([:positive])}"
      )

    File.mkdir_p!(directory)
    destination = Path.join(directory, "reader")
    File.cp!(library, destination <> ".so")

    case :erlang.load_nif(String.to_charlist(destination), 0) do
      :ok ->
        :persistent_term.put({__MODULE__, :parser}, parser)
        # Unix keeps the mapped image alive after unlinking this private copy.
        File.rm(destination <> ".so")
        File.rmdir(directory)
        :ok

      error ->
        raise "cannot load Rustler metadata reader: #{inspect(error)}"
    end
  end

  def read_exports(_library), do: :erlang.nif_error(:not_loaded)
end
