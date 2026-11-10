defmodule Lynx.Rust.OwnershipUnwind do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, LLBC}

  # The stock RustM backend propagates failure without executing MIR cleanup.
  # Only storage retirement followed by resumption is observationally empty.
  # In particular, a second destructor panic can abort the native process.
  def audit!(functions, translated, refs) do
    ids = MapSet.new(functions, & &1["def_id"])

    for function <- functions do
      owned =
        case function["body"] do
          %{"Structured" => %{"locals" => %{"locals" => locals}}} ->
            Enum.any?(locals, &owner?(CallModels.expand(&1["ty"], refs)))

          _ ->
            false
        end

      walk!(function["body"], owned, ids, function, translated)
    end
  end

  defp owner?(%{"Ref" => _}), do: false
  defp owner?(%{"Adt" => %{"builtin" => "Tuple", "generics" => %{"types" => []}}}), do: false
  defp owner?(type), do: not DropModels.primitive_scalar?(type)

  defp walk!(%{"on_unwind" => cleanup} = node, owned, ids, function, translated) do
    unless trivial?(cleanup),
      do:
        LLBC.failure!(
          function,
          translated,
          "explicit ownership requires empty observable unwind cleanup; destructor calls, mutation and abort during cleanup are unsupported"
        )

    node |> Map.delete("on_unwind") |> walk!(owned, ids, function, translated)
  end

  defp walk!(%{"BinaryOp" => [op, _, _]} = node, true, ids, function, translated) do
    unless op in ~w(BitAnd BitOr BitXor Eq Ne Lt Le Gt Ge),
      do:
        LLBC.failure!(
          function,
          translated,
          "explicit ownership rejects reconstructed fallible operations with owned locals: original overflow/bounds unwind edges are unavailable"
        )

    walk!(Map.values(node), false, ids, function, translated)
  end

  defp walk!(%{"UnaryOp" => [op, _]} = node, true, ids, function, translated) do
    unless op == "Not" or match?(%{"Cast" => %{"Scalar" => %{"Integer" => _}}}, op),
      do:
        LLBC.failure!(
          function,
          translated,
          "explicit ownership rejects reconstructed fallible unary operations with owned locals"
        )

    walk!(Map.values(node), false, ids, function, translated)
  end

  defp walk!(%{"Call" => %{"call" => %{"func" => func}}} = node, owned, ids, function, translated) do
    if owned do
      allowed =
        case func do
          %{"Regular" => %{"kind" => %{"Fun" => id}}} -> MapSet.member?(ids, id)
          %{"Regular" => %{"kind" => %{"Trait" => _}}} -> true
          _ -> false
        end

      unless allowed,
        do:
          LLBC.failure!(
            function,
            translated,
            "explicit ownership requires actual call bodies with owned locals; reconstructed or external call cleanup is unsupported"
          )
    end

    walk!(Map.values(node), owned, ids, function, translated)
  end

  defp walk!(%{"Index" => _}, true, _, function, translated),
    do:
      LLBC.failure!(
        function,
        translated,
        "explicit ownership rejects reconstructed indexing with owned locals"
      )

  defp walk!(%{"kind" => "UnwindTerminate"}, _, _, function, translated),
    do:
      LLBC.failure!(function, translated, "explicit ownership rejects native unwind termination")

  defp walk!(map, owned, ids, function, translated) when is_map(map),
    do: walk!(Map.values(map), owned, ids, function, translated)

  defp walk!(list, owned, ids, function, translated) when is_list(list),
    do: Enum.each(list, &walk!(&1, owned, ids, function, translated))

  defp walk!(_, _, _, _, _), do: :ok

  defp trivial?(%{"statements" => statements}) do
    case Enum.reverse(statements) do
      [%{"kind" => "UnwindResume"} | rest] ->
        Enum.all?(rest, &match?(%{"kind" => %{"StorageDead" => _}}, &1))

      _ ->
        false
    end
  end

  defp trivial?(_), do: false
end
