defmodule Lynx.Rust.Futures do
  @moduledoc false

  def arguments!(:reject, _tools), do: []

  def arguments!(:immediate, tools) do
    versions = File.read!(Path.join(tools, "lynx-toolchain")) |> String.split("\n")

    unless Enum.all?(["charon=", "aeneas="], fn prefix ->
             Enum.any?(
               versions,
               &(String.starts_with?(&1, prefix) and
                   String.ends_with?(&1, "+immediate-futures-v1"))
             )
           end),
           do:
             raise(
               ArgumentError,
               "immediate futures require the pinned immediate-futures-v1 backend"
             )

    [
      "--immediate-futures",
      "--monomorphize-mut=all",
      "--rustc-arg=-Zmir-strip-debuginfo=all-locals",
      "--rustc-arg=-Zmir-enable-passes=+DeadStoreElimination-final,+SimplifyLocals-final",
      "--include",
      "core::task::poll::Poll",
      "--include",
      "core::pin::Pin"
    ]
  end

  def arguments!(other, _tools),
    do: raise(ArgumentError, "unsupported Rust future extraction mode: #{inspect(other)}")

  def type_models!(:reject, _document), do: []

  def type_models!(:immediate, document) do
    contexts =
      Enum.filter(document["translated"]["type_decls"], fn type ->
        type &&
          type["item_meta"]["name"] ==
            Enum.map(~w(core task wake Context), &%{"Ident" => [&1, 0]})
      end)

    case contexts do
      [] ->
        []

      [
        %{
          "src" => "Normal",
          "kind" => "Opaque",
          "generics" => %{
            "types" => [],
            "const_generics" => [],
            "regions" => [_]
          }
        }
      ] ->
        [
          %{
            rust: "core::task::wake::Context",
            lean: "Unit",
            import: "Aeneas",
            label:
              "Unobserved task Context type: erased to Unit for immediate futures; waker access, suspension, cancellation and executor behavior are not admitted"
          }
        ]

      _ ->
        raise ArgumentError, "missing or ambiguous compiler task Context definition"
    end
  end
end
