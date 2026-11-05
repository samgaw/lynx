defmodule LynxRustFixture.CompositeNative do
  @compile :debug_info
  @on_load :load_nif

  def load_nif do
    path = Path.expand("../priv/libexperiment_composite", __DIR__)
    :erlang.load_nif(String.to_charlist(path), 0)
  end

  for name <- [
        :calculate,
        :restore,
        :negate,
        :echo_i8,
        :echo_i16,
        :echo_i32,
        :echo_u8,
        :echo_u16,
        :echo_u32,
        :echo_u64,
        :transform_pair,
        :classify,
        :reverse_result,
        :echo_nested,
        :echo_seven
      ] do
    def unquote(name)(_value), do: :erlang.nif_error(:not_loaded)
  end
end
