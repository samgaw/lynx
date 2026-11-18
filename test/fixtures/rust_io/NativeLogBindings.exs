defmodule LynxIoFixture.Native do
  @compile :debug_info

  def load(path), do: :erlang.load_nif(path, 0)
  def commit(_), do: :erlang.nif_error(:not_loaded)
  def log_reopen(_), do: :erlang.nif_error(:not_loaded)
  def log_try_reopen(_), do: :erlang.nif_error(:not_loaded)
  def log_create, do: :erlang.nif_error(:not_loaded)
  def log_repair_append(_, _, _), do: :erlang.nif_error(:not_loaded)
  def log_append(_, _), do: :erlang.nif_error(:not_loaded)
  def classify_end_of_file, do: :erlang.nif_error(:not_loaded)
  def classify_interrupted_read, do: :erlang.nif_error(:not_loaded)
  def read_retryable, do: :erlang.nif_error(:not_loaded)
  def read_exact_word, do: :erlang.nif_error(:not_loaded)
  def slice_word(_), do: :erlang.nif_error(:not_loaded)
end
