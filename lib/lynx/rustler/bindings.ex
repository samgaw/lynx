defmodule Lynx.Rustler.Bindings do
  @moduledoc false

  alias Lynx.Rust.LLBC

  # Join compiled exports, expanded Rustler signatures, extracted bodies and
  # Aeneas declaration identities. Names alone are never accepted as a model.
  def link!(manifest, audit, translation) do
    implementations = LLBC.link!(audit, translation)

    bindings =
      for binding <- manifest.bindings do
        functions = Enum.filter(audit.functions, &matches?(&1, audit.crate, binding))

        function =
          case functions do
            [function] ->
              function

            _ ->
              raise ArgumentError,
                    "missing or ambiguous extracted Rustler body for #{binding["name"]}/#{binding["arity"]}"
          end

        unless LLBC.signature!(function, audit) == {binding["arguments"], binding["result"]},
          do:
            raise(
              ArgumentError,
              "Rustler and LLBC signatures differ for #{binding["name"]}/#{binding["arity"]}"
            )

        implementation = Map.fetch!(implementations, function["def_id"])

        Map.merge(binding, %{
          "lean_name" => implementation["lean_name"],
          "definition_id" => function["def_id"],
          "lean_file" => implementation["lean_file"]
        })
      end

    %{manifest | bindings: bindings}
  end

  defp matches?(function, crate, binding) do
    expected_prefix = [crate | binding["modules"]]
    name = function["item_meta"]["name"]
    {prefix, tail} = Enum.split(name, length(expected_prefix))

    prefix_matches =
      Enum.zip(prefix, expected_prefix)
      |> Enum.all?(fn
        {%{"Ident" => [actual, _]}, expected} -> actual == expected
        _ -> false
      end)

    last_matches =
      case List.last(tail) do
        %{"Ident" => [name, _]} -> name == binding["rust_name"]
        _ -> false
      end

    length(prefix) == length(expected_prefix) && prefix_matches &&
      match?(
        [
          %{"Ident" => ["_", _]},
          %{"Ident" => ["__INVENTORY", _]},
          %{"Ident" => ["nif_func", _]},
          %{"Ident" => ["wrapper", _]},
          %{"Builtin" => ["Closure", _]},
          %{"Ident" => [_, _]}
        ],
        tail
      ) && last_matches
  end
end
