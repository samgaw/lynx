defmodule Lynx.Rust.Cargo do
  @moduledoc false

  @toolchain "nightly-2026-09-17"
  @recorder_manifest Path.expand("../../../native/rust_context/Cargo.toml", __DIR__)
  @libraries ~w(lib rlib cdylib dylib staticlib)

  def build!(manifest, package, directory, opts \\ []),
    do: compile!(manifest, package, directory, opts, nil)

  def metadata!(manifest, package, directory, opts, sysroot),
    do: compile!(manifest, package, directory, opts, sysroot)

  defp compile!(manifest, package, directory, opts, sysroot) do
    for key <- Keyword.keys(opts),
        key not in [:features, :default_features, :target, :profile],
        do: raise(ArgumentError, "unknown Rust build option: #{key}")

    manifest =
      Path.expand(if File.dir?(manifest), do: Path.join(manifest, "Cargo.toml"), else: manifest)

    directory = Path.expand(directory)

    effective_target = target!(opts, Path.dirname(manifest))

    opts = if sysroot, do: Keyword.put(opts, :target, effective_target), else: opts
    feature_args = feature_args(package, opts)
    metadata_args = feature_args ++ ["--filter-platform", effective_target]

    workspace =
      case Lynx.Rust.Workspace.discover(manifest, metadata_args, @toolchain) do
        {:ok, workspace} -> workspace
        {:error, message} -> raise ArgumentError, message
      end

    root =
      Enum.find(workspace.crates, &(&1.name == package)) ||
        raise(ArgumentError, "Rust proof root is not a workspace member: #{package}")

    target =
      case Enum.filter(root.targets, &Enum.any?(&1["kind"], fn kind -> kind in @libraries end)) do
        [target] ->
          target

        _ ->
          raise ArgumentError, "Rust proof roots currently require a library target: #{package}"
      end

    recorder = recorder!()

    compiler =
      command!("rustup", ["which", "--toolchain", @toolchain, "rustc"]) |> String.trim()

    crates = Lynx.Rust.LLBC.crate_names!(workspace)
    # A recorder change must also invalidate compiler metadata retained for dependencies.
    hash = digest(File.read!(recorder) <> if(sysroot, do: sysroot.fingerprint, else: "native"))
    target_dir = Path.join(directory, "cargo-" <> String.slice(hash, 0, 16))
    File.mkdir_p!(directory)
    record_file = Path.join(directory, "compiler.json")
    baseline_file = Path.join(directory, "baseline-#{System.unique_integer([:positive])}.json")
    baseline = Map.new(System.get_env(), fn {name, value} -> {name, digest(value)} end)
    File.write!(baseline_file, JSON.encode!(baseline))
    File.rm(record_file)
    cargo = ["run", @toolchain, "cargo"]

    try do
      # This directory belongs to verification. Rebuild the root to guarantee a
      # fresh compiler record; dependency compiler artifacts remain reusable.
      command!(
        "rustup",
        cargo ++
          [
            "clean",
            "--locked",
            "--manifest-path",
            manifest,
            "--package",
            package,
            "--target-dir",
            target_dir
          ] ++ if(opts[:target], do: ["--target", opts[:target]], else: []),
        cd: Path.dirname(manifest)
      )

      output =
        command!(
          "rustup",
          cargo ++
            [
              if(sysroot, do: "check", else: "build"),
              "--locked",
              "--manifest-path",
              manifest,
              "--package",
              package,
              "--lib",
              "--target-dir",
              target_dir,
              "--message-format=json"
            ] ++
            feature_args ++ build_args(opts),
          cd: Path.dirname(manifest),
          env: [
            {"RUSTC", recorder},
            {"LYNX_RECORD_COMPILER", compiler},
            {"LYNX_RECORD_CRATES", JSON.encode!(crates)},
            {"LYNX_RECORD_CRATE", target["name"]},
            {"LYNX_RECORD_FILE", record_file},
            {"LYNX_RECORD_BASELINE", baseline_file},
            {"LYNX_RECORD_SYSROOT", if(sysroot, do: sysroot.path, else: nil)}
          ]
        )

      artifacts =
        for line <- String.split(output, "\n"),
            {:ok, %{"reason" => "compiler-artifact"} = artifact} <- [JSON.decode(line)],
            do: artifact

      [artifact] =
        Enum.filter(
          artifacts,
          &(&1["package_id"] == root.id && &1["target"]["name"] == target["name"])
        )

      unless File.regular?(record_file),
        do: raise("Cargo did not invoke the compiler context recorder for #{package}")

      %{"version" => 1} = record = JSON.decode!(File.read!(record_file))

      context = %{
        baseline: baseline,
        record: record,
        workspace: workspace,
        package: root,
        artifact: artifact,
        artifacts: artifacts,
        directory: directory,
        toolchain: @toolchain,
        sysroot: sysroot
      }

      expected = command!("rustup", ["run", @toolchain, "rustc", "--version"])
      actual = replay!(context, ["--version"])

      unless actual == expected,
        do: raise("Cargo compiler differs from the pinned extraction compiler")

      context
    after
      File.rm(baseline_file)
    end
  end

  def target!(opts, directory) do
    target = opts[:target] || configured_target!(directory)

    case target do
      nil ->
        version = command!("rustup", ["run", @toolchain, "rustc", "-vV"])
        [_, host] = Regex.run(~r/^host: (.+)$/m, version)
        host

      target when is_binary(target) and target != "" ->
        target

      [target] when is_binary(target) and target != "" ->
        target

      _ ->
        raise ArgumentError, "Rust verification requires a single Cargo target"
    end
  end

  # Ask the pinned Cargo to resolve config-file and environment precedence.
  # Reading build.target only avoids capturing unrelated configuration secrets.
  defp configured_target!(directory) do
    arguments = [
      "run",
      @toolchain,
      "cargo",
      "-Zunstable-options",
      "config",
      "get",
      "build.target",
      "--format",
      "json-value"
    ]

    case System.cmd("rustup", arguments,
           cd: directory,
           stderr_to_stdout: true,
           env: [{"CARGO_TERM_COLOR", "never"}]
         ) do
      {output, 0} ->
        JSON.decode!(output)

      {output, 101} ->
        if String.contains?(output, "config value `build.target` is not set"),
          do: nil,
          else: raise("cannot resolve Cargo target:\n#{output}")

      {output, status} ->
        raise("cannot resolve Cargo target (#{status}):\n#{output}")
    end
  end

  def expand!(context) do
    replay!(context, context.record["arguments"] ++ ["-Zunpretty=expanded"], false)
  end

  def replay!(context, arguments, merge_stderr \\ true) do
    command!(context.record["compiler"], arguments,
      cd: context.record["directory"],
      env: environment(context),
      stderr_to_stdout: merge_stderr
    )
  end

  def environment(context) do
    overrides =
      MapSet.new(Map.keys(context.record["environment"]) ++ context.record["removed_environment"])

    current = System.get_env()

    for name <- Enum.uniq(Map.keys(context.baseline) ++ Map.keys(current)),
        not MapSet.member?(overrides, name) do
      value = current[name]

      unless is_binary(value) && context.baseline[name] == digest(value),
        do: raise("compiler environment changed since the native build: #{name}")
    end

    Map.to_list(context.record["environment"]) ++
      Enum.map(context.record["removed_environment"], &{&1, nil})
  end

  def extraction_arguments(context, output) do
    arguments = strip_output(context.record["arguments"])
    # Charon supplies the managed sysroot itself. Keep it in the original
    # record for direct compiler replay, but never pass rustc the option twice.
    arguments = if context[:sysroot], do: strip_sysroot(arguments), else: arguments
    arguments ++ ["--crate-type=rlib", "--emit=metadata", "--out-dir", Path.expand(output)]
  end

  defp strip_sysroot([]), do: []
  defp strip_sysroot(["--sysroot", _ | rest]), do: strip_sysroot(rest)
  defp strip_sysroot(["--sysroot=" <> _ | rest]), do: strip_sysroot(rest)
  defp strip_sysroot([argument | rest]), do: [argument | strip_sysroot(rest)]

  defp strip_output([]), do: []

  defp strip_output([flag, _value | tail]) when flag in ["--crate-type", "--emit", "--out-dir"],
    do: strip_output(tail)

  defp strip_output(["-C", "incremental=" <> _ | tail]), do: strip_output(tail)

  defp strip_output([argument | tail]) do
    if Enum.any?(
         ["--crate-type=", "--emit=", "--out-dir=", "-Cincremental="],
         &String.starts_with?(argument, &1)
       ), do: strip_output(tail), else: [argument | strip_output(tail)]
  end

  defp feature_args(package, opts) do
    features = Keyword.get(opts, :features, [])

    unless Enum.all?(features, &(is_binary(&1) && !String.contains?(&1, "/"))),
      do: raise(ArgumentError, "Rust features must be names in the selected workspace package")

    flags = if Keyword.get(opts, :default_features, true), do: [], else: ["--no-default-features"]

    flags ++
      if(features == [],
        do: [],
        else: ["--features", Enum.map_join(features, ",", &(package <> "/" <> &1))]
      )
  end

  defp build_args(opts) do
    if(opts[:target], do: ["--target", opts[:target]], else: []) ++
      if(opts[:profile], do: ["--profile", opts[:profile]], else: [])
  end

  defp recorder! do
    output =
      command!("cargo", [
        "build",
        "--locked",
        "--manifest-path",
        @recorder_manifest,
        "--message-format=json"
      ])

    [path] =
      for line <- String.split(output, "\n"),
          {:ok,
           %{
             "reason" => "compiler-artifact",
             "target" => %{"name" => "lynx-rust-context"},
             "executable" => path
           }}
          when is_binary(path) <- [JSON.decode(line)],
          do: path

    path
  end

  defp command!(executable, arguments, opts \\ []) do
    {output, status} =
      System.cmd(executable, arguments, Keyword.put_new(opts, :stderr_to_stdout, true))

    if status != 0, do: raise("#{executable} failed (#{status}):\n#{output}")
    output
  end

  defp digest(value), do: :crypto.hash(:sha256, value) |> Base.encode16(case: :lower)
end
