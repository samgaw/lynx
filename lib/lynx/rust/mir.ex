defmodule Lynx.Rust.Mir do
  @moduledoc false

  def validate!(opts) do
    stage = opts[:mir]

    unless is_nil(stage) or stage in [:promoted, :elaborated, :optimized],
      do: raise(ArgumentError, "mir must be :promoted, :elaborated or :optimized")

    if stage && (opts[:owned_drops] == true or Keyword.get(opts, :execution, :pure) != :pure),
      do:
        raise(
          ArgumentError,
          "explicit mir selection currently requires pure execution without owned_drops"
        )

    :ok
  end

  def arguments!(opts) do
    validate!(opts)

    cond do
      opts[:mir] -> ["--mir", Atom.to_string(opts[:mir])]
      opts[:owned_drops] == true and opts[:futures] != :cancelling -> ["--mir", "optimized"]
      true -> []
    end
  end
end
