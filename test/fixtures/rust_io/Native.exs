defmodule LynxIoFixture.Native do
  @compile :debug_info
  @on_load :load
  def load, do: :erlang.load_nif(to_charlist(__LIBRARY__), 0)
  def commit(_value), do: :erlang.nif_error(:not_loaded)
end
