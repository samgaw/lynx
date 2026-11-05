defmodule Lynx.Rust do
  @moduledoc """
  Verifies properties of first-party Cargo workspace implementations without Rustler.

  Roots are Rust paths, selected for extraction with their reachable first-party
  definitions. Proof modules contain ordinary Lean theorems over those generated
  definitions. The checked report discovers which implementations each theorem
  actually mentions; extracted bodies without properties are never called verified.
  """

  @doc """
  Builds, extracts and kernel-checks workspace properties.

  Required option `:roots` lists Rust paths. `:proof_modules` lists Lean modules
  containing properties; `:required_properties` can require particular theorem
  names, rejecting missing or unrelated theorems. Every supplied module is audited
  in full, including private and unused declarations.

  `:lean_project` defaults to `lynx-proofs` in the workspace and is initialized
  with the pinned runtime when needed. `:module_prefix` defaults to
  `Native.Extraction`. Also accepts `:tools` (or `LYNX_AENEAS_DIR`), `:build_dir`
  and `:cargo` options as in `Lynx.Rustler.prepare!/3`.
  """
  def verify!(workspace, package, opts) do
    Lynx.External.with_preparation_lock(fn -> do_verify!(workspace, package, opts) end)
  end

  defp do_verify!(workspace, package, opts) do
    allowed = [
      :roots,
      :proof_modules,
      :required_properties,
      :lean_project,
      :module_prefix,
      :tools,
      :build_dir,
      :cargo
    ]

    for key <- Keyword.keys(opts),
        key not in allowed,
        do: raise(ArgumentError, "unknown Rust verification option: #{key}")

    roots = Keyword.fetch!(opts, :roots)
    tools = opts[:tools] || System.fetch_env!("LYNX_AENEAS_DIR")
    prefix = Keyword.get(opts, :module_prefix, "Native.Extraction")
    proofs = Keyword.get(opts, :proof_modules, [])
    directory = opts[:build_dir] || Path.join([Mix.Project.build_path(), "lynx", "rust", package])
    context = Lynx.Rust.Cargo.build!(workspace, package, directory, Keyword.get(opts, :cargo, []))

    project =
      Lynx.Rust.Project.ensure!(
        opts[:lean_project] || Path.join(context.workspace.root, "lynx-proofs"),
        prefix,
        tools
      )

    extraction = Lynx.Rust.Extraction.run!(context, tools, roots, project, prefix)
    Lynx.Rust.Project.build!(project, [prefix <> ".Funs" | proofs])

    file =
      Lynx.Rust.Proofs.file!(extraction, proofs,
        required_properties: Keyword.get(opts, :required_properties, [])
      )

    files =
      Lynx.Translation.new(
        externals: [
          %Lynx.External{bindings: [], files: [file], fingerprint: extraction.fingerprint}
        ]
      )
      |> Lynx.Translation.assemble()

    reports = Lynx.Commands.verify!(project, files)

    unless Enum.all?(reports, &(&1.status == :ok)),
      do:
        raise(
          "Rust properties or proof audit failed:\n#{inspect(reports, pretty: true, limit: :infinity)}"
        )

    %{
      reports: reports,
      verification:
        Lynx.Rust.Report.build!(extraction, reports, source_dir: context.record["directory"]),
      extraction: extraction,
      context: context,
      project: project
    }
  end
end
