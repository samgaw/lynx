defmodule LynxWorkspaceExample do
  @root __DIR__

  def options do
    [
      workspace: Path.join(@root, "native"),
      package: "example-nif",
      lean_project: Path.join(@root, "proofs"),
      module_prefix: "WorkspaceExample.Extraction",
      build_dir: Path.join(@root, ".build"),
      proof_modules: ["WorkspaceExample.Properties"],
      required_properties: [
        "WorkspaceExample.Properties.invert_spec",
        "WorkspaceExample.Properties.analysis_spec",
        "WorkspaceExample.Properties.facade_spec"
      ]
    ]
  end

  def load_native!(library) do
    directory = Path.join(@root, ".build/beam")
    File.mkdir_p!(directory)
    File.cp!(library, Path.join(@root, ".build/example_nif.so"))

    case Kernel.ParallelCompiler.compile_to_path(
           [Path.join(@root, "elixir/native.ex")],
           directory,
           return_diagnostics: true
         ) do
      {:ok, [LynxWorkspaceExample.Native], _} -> :ok
      error -> raise "native module compilation failed: #{inspect(error)}"
    end
  end
end
