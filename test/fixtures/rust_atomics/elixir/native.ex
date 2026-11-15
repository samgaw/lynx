defmodule LynxAtomicFixture.Native do
  @compile :debug_info
  @on_load :load_nif
  def load_nif do
    path = Path.expand("../priv/libatomic_nif", __DIR__)
    :erlang.load_nif(String.to_charlist(path), 0)
  end

  def atomic_new(_value), do: :erlang.nif_error(:not_loaded)
  def atomic_claim(_resource), do: :erlang.nif_error(:not_loaded)
  def atomic_pair(_resource), do: :erlang.nif_error(:not_loaded)
  def atomic_read(_resource), do: :erlang.nif_error(:not_loaded)
  def atomic_result(_resource, _mode), do: :erlang.nif_error(:not_loaded)
  def atomic_replace(_resource, _expected, _replacement), do: :erlang.nif_error(:not_loaded)
  def atomic_checked(_value, _accepted), do: :erlang.nif_error(:not_loaded)
end
