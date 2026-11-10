defmodule LynxOwnershipFixture.Native do
  @compile :debug_info
  @on_load :load_nif
  def load_nif do
    path = Path.expand("../priv/libownership_nif", __DIR__)
    :erlang.load_nif(String.to_charlist(path), 0)
  end

  def checked_code(_value), do: :erlang.nif_error(:not_loaded)
  def scalar_code(_value), do: :erlang.nif_error(:not_loaded)
end
