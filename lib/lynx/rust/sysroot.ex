defmodule Lynx.Rust.Sysroot do
  @moduledoc false

  def validate!(opts) do
    unless Keyword.get(opts, :sysroot, :default) in [:default, :full_mir],
      do: raise(ArgumentError, "Rust sysroot must be :default or :full_mir")

    if opts[:sysroot] == :full_mir and Keyword.get(opts, :execution, :pure) != :pure,
      do: raise(ArgumentError, "full-MIR sysroot currently requires pure execution")
  end

  # An explicit target also changes Cargo's host Rust-flags handling. Use the
  # same setting for both native and metadata builds, including host==target.
  def cargo_options!(opts, workspace) do
    directory = if File.dir?(workspace), do: workspace, else: Path.dirname(workspace)
    cargo = opts[:cargo] || []

    if opts[:sysroot] == :full_mir do
      target = Lynx.Rust.Cargo.target!(cargo, directory)

      unless Regex.match?(~r/\A[A-Za-z0-9_][A-Za-z0-9_-]*\z/, target),
        do:
          raise(
            ArgumentError,
            "full-MIR extraction requires a named Rust target, not a target file"
          )

      Keyword.put(cargo, :target, target)
    else
      cargo
    end
  end

  # Native compilation remains separate: Miri's full-MIR libraries cannot
  # generate the Rustler shared library. Rebuild all target metadata together;
  # mixing default-sysroot dependency artifacts is rejected by rustc.
  def context!(native, workspace, package, directory, tools, opts) do
    validate!(opts)

    case Keyword.get(opts, :sysroot, :default) do
      :default ->
        native

      :full_mir ->
        charon = Path.join(Path.expand(tools), "charon")
        toolchain = command!(charon, ["toolchain-version"])

        unless toolchain == native.toolchain,
          do: raise(ArgumentError, "full-MIR sysroot compiler differs from the native compiler")

        target = Keyword.fetch!(cargo_options!(opts, workspace), :target)

        unless Enum.chunk_every(native.record["arguments"], 2, 1, :discard)
               |> Enum.member?(["--target", target]),
               do:
                 raise(
                   ArgumentError,
                   "full-MIR extraction requires the same explicit native Cargo target"
                 )

        arguments = ["--target", target]
        path = command!(charon, ["print-sysroot" | arguments])
        default = command!("rustup", ["run", native.toolchain, "rustc", "--print", "sysroot"])

        # print-sysroot may fall back after setup fails. Never silently claim
        # full-MIR support for the distributed libraries.
        if path == default or Path.type(path) != :absolute,
          do: raise(ArgumentError, "Charon did not provide a full-MIR sysroot")

        libraries =
          Path.wildcard(Path.join([path, "lib", "rustlib", "*", "lib", "*"]))
          |> Enum.filter(&(Path.extname(&1) in [".rmeta", ".rlib", ".so", ".dylib", ".dll"]))
          |> Enum.sort()

        if not Enum.any?(libraries, &(Path.extname(&1) == ".rmeta")),
          do: raise(ArgumentError, "full-MIR sysroot has no standard-library metadata: #{path}")

        fingerprint =
          libraries
          |> Enum.map(&{&1, Lynx.Rust.Fingerprint.file!(&1)})
          |> :erlang.term_to_binary([:deterministic])
          |> Lynx.Rust.Fingerprint.digest()

        context =
          Lynx.Rust.Cargo.metadata!(
            workspace,
            package,
            Path.join(directory, "full-mir"),
            cargo_options!(opts, workspace),
            %{path: path, fingerprint: fingerprint}
          )

        unless context.workspace == native.workspace and
                 context.package.id == native.package.id and
                 context.artifact["target"] == native.artifact["target"] and
                 context.artifact["features"] == native.artifact["features"] and
                 context.artifact["profile"] == native.artifact["profile"],
               do:
                 raise(
                   ArgumentError,
                   "full-MIR metadata differs from the native Cargo configuration"
                 )

        context
    end
  end

  defp command!(executable, arguments) do
    case System.cmd(executable, arguments) do
      {output, 0} -> String.trim(output)
      {output, status} -> raise "Rust sysroot command failed (#{status}):\n#{output}"
    end
  end
end
