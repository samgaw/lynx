defmodule LynxRustFixture.Native do
  @compile :debug_info
  @on_load :load_nif
  def load_nif do
    path = Path.expand("../priv/libexperiment_nif", __DIR__)
    :erlang.load_nif(String.to_charlist(path), 0)
  end

  def negate(_value), do: :erlang.nif_error(:not_loaded)
  def restore(_value), do: :erlang.nif_error(:not_loaded)

  def restored(value), do: restore(value)
  def restored_remotely(value), do: __MODULE__.restore(value)
  def restore_fun, do: &restore/1

  def restored_by_fun(value) do
    fun = restore_fun()
    fun.(value)
  end

  def unverified_echo(value), do: echo_i8(value)

  for name <- [
        :calculate,
        :echo_i8,
        :echo_i16,
        :echo_i32,
        :echo_u8,
        :echo_u16,
        :echo_u32,
        :echo_u64
      ] do
    def unquote(name)(_value), do: :erlang.nif_error(:not_loaded)
  end
end
