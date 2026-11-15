defmodule LynxAtomicFixture.Native do
  @compile :debug_info
  @on_load :load_nif
  def load_nif do
    path = Path.expand("../priv/libatomic_nif", __DIR__)
    :erlang.load_nif(String.to_charlist(path), 0)
  end

  def consume_chunks(_, _, _), do: :erlang.nif_error(:not_loaded)

  def signed_adjust(_, _), do: :erlang.nif_error(:not_loaded)

  def atomic_new(_value), do: :erlang.nif_error(:not_loaded)
  def atomic_claim(_resource), do: :erlang.nif_error(:not_loaded)
  def atomic_pair(_resource), do: :erlang.nif_error(:not_loaded)
  def atomic_read(_resource), do: :erlang.nif_error(:not_loaded)
  def atomic_command(_, _), do: :erlang.nif_error(:not_loaded)
  def atomic_scalar(_, _), do: :erlang.nif_error(:not_loaded)
  def scalar_bool(_), do: :erlang.nif_error(:not_loaded)
  def scalar_i8(_), do: :erlang.nif_error(:not_loaded)
  def scalar_i16(_), do: :erlang.nif_error(:not_loaded)
  def scalar_i32(_), do: :erlang.nif_error(:not_loaded)
  def scalar_i64(_), do: :erlang.nif_error(:not_loaded)
  def scalar_u8(_), do: :erlang.nif_error(:not_loaded)
  def scalar_u16(_), do: :erlang.nif_error(:not_loaded)
  def scalar_u32(_), do: :erlang.nif_error(:not_loaded)
  def scalar_u64(_), do: :erlang.nif_error(:not_loaded)

  def atomic_map(_, _), do: :erlang.nif_error(:not_loaded)
  def atomic_struct(_, _), do: :erlang.nif_error(:not_loaded)

  def atomic_tuple(_resource, _request), do: :erlang.nif_error(:not_loaded)
  def atomic_decoded(_resource, _request, _enabled), do: :erlang.nif_error(:not_loaded)
  def atomic_decoded_first(_request, _resource), do: :erlang.nif_error(:not_loaded)
  def atomic_result(_resource, _mode), do: :erlang.nif_error(:not_loaded)
  def atomic_replace(_resource, _expected, _replacement), do: :erlang.nif_error(:not_loaded)
  def atomic_checked(_value, _accepted), do: :erlang.nif_error(:not_loaded)
  def atomic_reply(_resource, _expected, _replacement), do: :erlang.nif_error(:not_loaded)

  def atomic_reply_option(_resource, _expected, _replacement), do: :erlang.nif_error(:not_loaded)

  def atomic_reply_result(_resource, _expected, _replacement), do: :erlang.nif_error(:not_loaded)

  def atomic_reply_tuple(_resource, _expected, _replacement), do: :erlang.nif_error(:not_loaded)

  def atomic_reply_checked(_resource, _expected, _replacement), do: :erlang.nif_error(:not_loaded)

  def atomic_reply_nif_result(_resource, _expected, _replacement),
    do: :erlang.nif_error(:not_loaded)

  def buffer_new(_, _), do: :erlang.nif_error(:not_loaded)
  def buffer_length(_), do: :erlang.nif_error(:not_loaded)
  def buffer_head(_), do: :erlang.nif_error(:not_loaded)
  def buffer_copy(_), do: :erlang.nif_error(:not_loaded)
  def buffer_copy_locked(_), do: :erlang.nif_error(:not_loaded)
  def frame_summary(_), do: :erlang.nif_error(:not_loaded)
  def frame_split(_, _), do: :erlang.nif_error(:not_loaded)
  def shared_new(), do: :erlang.nif_error(:not_loaded)
  def shared_append(_, _), do: :erlang.nif_error(:not_loaded)
  def shared_read(_), do: :erlang.nif_error(:not_loaded)
end
