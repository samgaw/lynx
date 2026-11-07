defmodule Lynx.Rustler.NifFixture do
  @moduledoc false

  # The compiler's conflict check can autoload an old fixture after it has been
  # purged, turning a fresh load into an unsupported NIF upgrade. These fixture
  # compilations run in synchronous tests; restore the global option afterwards.
  def compile!(source, destination, module) do
    previous = Code.compiler_options()[:ignore_module_conflict]

    try do
      Code.compiler_options(ignore_module_conflict: true)

      result =
        Kernel.ParallelCompiler.compile_to_path([source], destination, return_diagnostics: true)

      {:module, ^module} = Code.ensure_loaded(module)
      result
    after
      Code.compiler_options(ignore_module_conflict: previous)
    end
  end
end
