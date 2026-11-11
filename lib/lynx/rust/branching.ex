defmodule Lynx.Rust.Branching do
  @moduledoc false

  def validate!(opts) do
    mode = Keyword.get(opts, :branching, :join)

    unless mode in [:join, :duplicate],
      do: raise(ArgumentError, "branching must be :join or :duplicate")

    mode
  end

  def backend_arguments!(opts, tools) do
    case validate!(opts) do
      :join ->
        []

      :duplicate ->
        unless "aeneas_branching=duplicate-v1" in String.split(
                 File.read!(Path.join(tools, "lynx-toolchain")),
                 "\n"
               ),
               do:
                 raise(
                   ArgumentError,
                   "branching: :duplicate requires the branch-duplication backend"
                 )

        ["-duplicate-branches"]
    end
  end

  def validate_metadata!(translation, opts) do
    expected = validate!(opts) == :join

    unless Map.get(translation, "branch_joins", true) == expected,
      do: raise(ArgumentError, "Rust backend branch mode does not match the requested extraction")

    :ok
  end
end
