defmodule LynxIoFixture.Native do
  @compile :debug_info

  def load(path), do: :erlang.load_nif(path, 0)
  def commit(_), do: :erlang.nif_error(:not_loaded)
  def log_reopen(_), do: :erlang.nif_error(:not_loaded)
  def log_create, do: :erlang.nif_error(:not_loaded)
  def log_append(_, _), do: :erlang.nif_error(:not_loaded)
end
