defmodule Lynx.Rustler.AtomInitializer do
  @moduledoc false

  # Validate the literal-to-field join in the compiled initializer, independently
  # of the field order in a separate procedural-macro expansion. This recognizes
  # only Rustler's straight-line initializer; it does not translate Rust bodies.
  def fields!(functions, type_id, fields, literals, constructors, expects) do
    results =
      for function <- functions,
          %{"Structured" => %{"body" => %{"statements" => statements}}} <- [function["body"]],
          constructs?(statements, type_id) do
        unless List.last(statements)["kind"] == "Return" and
                 Enum.all?(Enum.drop(statements, -1), &(&1["kind"] != "Return")),
               do: fail!()

        values =
          Enum.reduce(statements, %{}, fn statement, locals ->
            case statement["kind"] do
              %{"Assign" => [%{"kind" => %{"Local" => id}}, expression]} ->
                Map.put(locals, id, expression(expression, locals, literals, type_id))

              %{
                "Call" => %{
                  "call" => %{
                    "func" => %{"Regular" => %{"kind" => %{"Fun" => id}}},
                    "args" => args
                  },
                  "dest" => %{"kind" => %{"Local" => dest}}
                }
              } ->
                value =
                  cond do
                    id in constructors ->
                      case args do
                        [_, text] ->
                          case operand(text, locals) do
                            {:literal, atom} -> {:pending, atom}
                            _ -> fail!()
                          end

                        _ ->
                          fail!()
                      end

                    id in expects ->
                      case args do
                        [source, _] ->
                          case operand(source, locals) do
                            {:pending, atom} -> {:atom, atom}
                            _ -> fail!()
                          end

                        _ ->
                          fail!()
                      end

                    true ->
                      fail!()
                  end

                Map.put(locals, dest, value)

              %{"StorageLive" => _} ->
                locals

              %{"StorageDead" => _} ->
                locals

              "Nop" ->
                locals

              "Return" ->
                locals

              _ ->
                fail!()
            end
          end)

        case values[0] do
          {:fields, atoms} when length(atoms) == length(fields) ->
            Enum.zip_with(fields, atoms, fn field, value ->
              case value do
                {:atom, atom} -> %{"field" => field["name"], "atom" => atom}
                _ -> fail!()
              end
            end)

          _ ->
            fail!()
        end
      end

    case results do
      [fields] -> fields
      _ -> fail!()
    end
  end

  defp constructs?(statements, id) do
    Enum.any?(statements, fn
      %{
        "kind" => %{
          "Assign" => [_, %{"Aggregate" => [%{"Adt" => [%{"id" => ^id}, nil, nil]}, _]}]
        }
      } ->
        true

      _ ->
        false
    end)
  end

  defp expression(%{"Use" => [source, _]}, locals, _literals, _id), do: operand(source, locals)

  defp expression(%{"Ref" => %{"place" => place, "kind" => "Shared"}}, locals, literals, _id),
    do: place(place, locals, literals)

  defp expression(
         %{"Aggregate" => [%{"Adt" => [%{"id" => id}, nil, nil]}, args]},
         locals,
         _literals,
         id
       ),
       do: {:fields, Enum.map(args, &operand(&1, locals))}

  defp expression(_, _, _, _), do: nil

  defp operand(%{"Copy" => place}, locals), do: place(place, locals, %{})
  defp operand(%{"Move" => place}, locals), do: place(place, locals, %{})
  defp operand(_, _), do: nil

  defp place(%{"kind" => %{"Local" => id}}, locals, _literals), do: locals[id]

  defp place(%{"kind" => %{"Projection" => [base, "Deref"]}}, locals, literals),
    do: place(base, locals, literals)

  defp place(%{"kind" => %{"Global" => %{"id" => id}}}, _locals, literals),
    do: if(Map.has_key?(literals, id), do: {:literal, literals[id]})

  defp place(_, _, _), do: nil

  defp fail!,
    do: raise(ArgumentError, "unsupported compiled Rustler atom initializer field bindings")
end
