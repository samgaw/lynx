defmodule Lynx.Rust.NativeOwnedDrops do
  @moduledoc false

  def arguments!(false, _), do: []

  def arguments!(true, tools) do
    versions = File.read!(Path.join(tools, "lynx-toolchain")) |> String.split("\n")

    unless Enum.any?(
             versions,
             &(String.starts_with?(&1, "charon=") and "owned-drops-v1" in String.split(&1, "+"))
           ),
           do:
             raise(ArgumentError, "owned destruction requires the pinned owned-drops-v1 compiler")

    ["--owned-drops"]
  end

  def arguments!(other, _),
    do: raise(ArgumentError, "invalid owned_drops option: #{inspect(other)}")
end
