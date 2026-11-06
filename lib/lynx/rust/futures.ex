defmodule Lynx.Rust.Futures do
  @moduledoc false

  def arguments!(:reject, _tools), do: []

  def arguments!(mode, tools) when mode in [:immediate, :polling, :suspending, :cancelling] do
    versions = File.read!(Path.join(tools, "lynx-toolchain")) |> String.split("\n")

    unless Enum.all?(["charon=", "aeneas="], fn prefix ->
             Enum.any?(
               versions,
               &(String.starts_with?(&1, prefix) and
                   Enum.member?(String.split(&1, "+"), "immediate-futures-v1"))
             )
           end),
           do:
             raise(
               ArgumentError,
               "immediate futures require the pinned immediate-futures-v1 backend"
             )

    if mode in [:suspending, :cancelling] and
         not Enum.all?(
           [{"charon=", "suspending-futures-v1"}, {"aeneas=", "undefined-behavior-v1"}],
           fn {prefix, capability} ->
             Enum.any?(
               versions,
               &(String.starts_with?(&1, prefix) and capability in String.split(&1, "+"))
             )
           end
         ),
       do:
         raise(
           ArgumentError,
           "suspending futures require the pinned suspending-futures-v1 and undefined-behavior-v1 backends"
         )

    if mode == :cancelling and
         not Enum.any?(
           versions,
           &(String.starts_with?(&1, "charon=") and
               "cancelling-futures-v1" in String.split(&1, "+"))
         ),
       do:
         raise(
           ArgumentError,
           "coroutine destruction requires the pinned cancelling-futures-v1 backend"
         )

    if(mode == :cancelling, do: ["--cancelling-futures", "--mir", "optimized"], else: []) ++
      if(mode in [:suspending, :cancelling], do: ["--suspending-futures"], else: []) ++
      [
        "--immediate-futures",
        "--monomorphize-mut=all",
        "--rustc-arg=-Zmir-strip-debuginfo=all-locals",
        "--rustc-arg=-Zmir-enable-passes=+DeadStoreElimination-final,+SimplifyLocals-final",
        "--include",
        "core::task::poll::Poll",
        "--include",
        "core::pin",
        "--include",
        "core::future::future::Future",
        "--include",
        "core::future::into_future",
        "--include",
        "core::option::Option"
      ]
  end

  def arguments!(other, _tools),
    do: raise(ArgumentError, "unsupported Rust future extraction mode: #{inspect(other)}")

  def type_models!(mode, document, prefix \\ "Native.Extraction")
  def type_models!(:reject, _document, _prefix), do: []

  def type_models!(:immediate, document, _prefix) do
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

  def type_models!(mode, document, prefix) when mode in [:polling, :suspending, :cancelling] do
    module = (prefix |> String.split(".") |> hd()) <> ".NativeRuntime"

    for {name, lean} <- [{"Context", "Lynx.NativeTaskContext"}, {"Waker", "Lynx.NativeWaker"}] do
      unless Lynx.Rust.FutureModels.type(document["translated"], name),
        do: raise(ArgumentError, "stateful polling requires the compiler #{name} definition")

      %{
        rust: "core::task::wake::" <> name,
        lean: lean,
        import: module,
        label:
          "Registered native " <>
            name <>
            " model; borrowed wake capability, coalesced notification; callback registration, physical layout and executor correctness unverified"
      }
    end
  end
end
