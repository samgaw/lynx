defmodule LynxWorkspaceExample.Native do
  @compile :debug_info
  @on_load :load_nif

  def load_nif do
    path = Path.expand("../.build/example_nif", __DIR__)
    :erlang.load_nif(String.to_charlist(path), 0)
  end

  def restore(_value), do: :erlang.nif_error(:not_loaded)
end
