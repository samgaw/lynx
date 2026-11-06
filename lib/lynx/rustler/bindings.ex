defmodule Lynx.Rustler.Bindings do
  @moduledoc false

  alias Lynx.Rust.LLBC

  def custom?(%{"native" => _}), do: true
  def custom?(map) when is_map(map), do: Enum.any?(Map.values(map), &custom?/1)
  def custom?(list) when is_list(list), do: Enum.any?(list, &custom?/1)
  def custom?(_), do: false

  # Expanded paths can be aliases. The compiled function's actual result type
  # determines identity; only monomorphic first-party structs/enums qualify.
  def resolve!(manifest, document, first_party, models \\ []) do
    audit = %{
      crate: document["translated"]["crate_name"],
      translated: document["translated"],
      functions: Enum.reject(document["translated"]["fun_decls"], &is_nil/1),
      references: LLBC.type_references!(document),
      first_party: first_party,
      external_types: models
    }

    bindings =
      for binding <- manifest.bindings do
        function = function!(audit, binding)
        signature = function["signature"]

        unless Enum.map(signature["inputs"], &LLBC.nif_type!(&1, audit)) == binding["arguments"],
          do: raise(ArgumentError, "Rustler and compiled argument signatures differ")

        Map.put(
          binding,
          "result",
          result!(binding["result"], signature["output"], audit, :discover, nil)
        )
      end

    %{manifest | bindings: bindings}
  end

  def encoder_roots(manifest) do
    manifest.bindings
    |> Enum.flat_map(&native_types(&1["result"]))
    |> Enum.uniq()
    |> Enum.map(&("{impl rustler::Encoder for " <> Enum.join(&1, "::") <> "}::encode"))
  end

  defp native_types(%{"native" => name}), do: [name]
  defp native_types(map) when is_map(map), do: Enum.flat_map(Map.values(map), &native_types/1)
  defp native_types(list) when is_list(list), do: Enum.flat_map(list, &native_types/1)
  defp native_types(_), do: []

  # Join compiled exports, expanded Rustler signatures, extracted bodies and
  # Aeneas declaration identities. Names alone are never accepted as a model.
  def link!(manifest, audit, translation, opts \\ []) do
    implementations = LLBC.link!(audit, translation, opts)

    bindings =
      for binding <- manifest.bindings do
        function = function!(audit, binding)
        signature = function["signature"]

        arguments =
          Enum.zip_with(binding["arguments"], signature["inputs"], fn hint, type ->
            argument!(hint, type, audit, translation, Keyword.get(opts, :resource_types, []))
          end)

        unless length(arguments) == length(signature["inputs"]) and
                 length(arguments) == binding["arity"],
               do: raise(ArgumentError, "Rustler and LLBC argument counts differ")

        implementation = Map.fetch!(implementations, function["def_id"])

        Map.merge(binding, %{
          "arguments" => arguments,
          "result" =>
            if(match?(%{"resource" => _}, binding["result"]),
              do:
                resource!(
                  binding["result"],
                  signature["output"],
                  audit,
                  Keyword.get(opts, :resource_types, [])
                ),
              else: result!(binding["result"], signature["output"], audit, :link, translation)
            ),
          "lean_name" => implementation["lean_name"],
          "definition_id" => function["def_id"],
          "lean_file" => implementation["lean_file"]
        })
      end

    %{manifest | bindings: bindings}
  end

  defp argument!(%{"resource" => _} = hint, type, audit, _translation, resources),
    do: resource!(hint, type, audit, resources)

  defp argument!(hint, type, audit, _translation, _resources) do
    unless LLBC.nif_type!(type, audit) == hint,
      do: raise(ArgumentError, "Rustler and LLBC argument signatures differ")

    hint
  end

  defp resource!(_hint, type, audit, resources) do
    path =
      case LLBC.nif_type!(type, audit) do
        %{"resource" => path} ->
          path

        _ ->
          raise ArgumentError,
                "resource signature must resolve to the actual Rustler ResourceArc type"
      end

    case Enum.filter(resources, &(&1.rust_name == Enum.join(path, "::"))) do
      [resource] ->
        %{"resource" => path, "lean" => resource.lean_name}

      _ ->
        raise ArgumentError,
              "resource signature requires a validated registration and audited concrete Resource implementation"
    end
  end

  defp result!(%{"native" => hint}, type, audit, mode, translation) do
    resolved = Lynx.Rust.CallModels.expand(type, audit.references)

    with %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => generics}} <- resolved,
         true <- Lynx.Rust.Constants.empty_arguments?(generics),
         %{"item_meta" => %{"name" => name}, "kind" => kind, "generics" => params} <-
           Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id)),
         true <- is_map(kind) and (Map.has_key?(kind, "Struct") or Map.has_key?(kind, "Enum")),
         true <- Enum.all?(Map.values(params), &(&1 == [])),
         true <- Enum.all?(name, &match?(%{"Ident" => [_, 0]}, &1)),
         path = Enum.map(name, fn %{"Ident" => [part, 0]} -> part end),
         true <- hd(path) in audit.first_party,
         true <- mode == :discover or hint == path do
      if mode == :discover,
        do: %{"native" => path},
        else:
          Map.merge(
            %{"native" => path},
            Lynx.Rustler.EncoderModels.binding!(id, audit, translation)
          )
    else
      _ ->
        raise ArgumentError,
              "custom NIF result requires its actual monomorphic first-party struct/enum and matching extracted Encoder"
    end
  end

  defp result!(%{"result" => [ok, err]}, type, audit, mode, translation) do
    case Lynx.Rust.CallModels.expand(type, audit.references) do
      %{
        "Adt" => %{
          "id" => id,
          "builtin" => nil,
          "generics" => %{
            "types" => [ok_type, err_type],
            "regions" => [],
            "const_generics" => [],
            "trait_refs" => []
          }
        }
      } ->
        unless LLBC.result_type?(id, audit),
          do: raise(ArgumentError, "NIF result is not the extracted core::result::Result")

        %{
          "result" => [
            result!(ok, ok_type, audit, mode, translation),
            result!(err, err_type, audit, mode, translation)
          ]
        }

      _ ->
        raise ArgumentError, "Rustler and compiled Result signatures differ"
    end
  end

  defp result!(%{"tuple" => fields}, type, audit, mode, translation) do
    case Lynx.Rust.CallModels.expand(type, audit.references) do
      %{
        "Adt" => %{
          "builtin" => "Tuple",
          "generics" => %{
            "types" => types,
            "regions" => [],
            "const_generics" => [],
            "trait_refs" => []
          }
        }
      }
      when length(types) == length(fields) and length(types) <= 7 ->
        %{"tuple" => Enum.zip_with(fields, types, &result!(&1, &2, audit, mode, translation))}

      _ ->
        raise ArgumentError, "Rustler and compiled tuple signatures differ"
    end
  end

  defp result!(schema, type, audit, _mode, _translation) do
    unless LLBC.nif_type!(type, audit) == schema,
      do: raise(ArgumentError, "Rustler and LLBC signatures differ: result type")

    schema
  end

  defp function!(audit, binding) do
    case Enum.filter(audit.functions, &matches?(&1, audit.crate, binding)) do
      [function] ->
        function

      _ ->
        raise ArgumentError,
              "missing or ambiguous extracted Rustler body for #{binding["name"]}/#{binding["arity"]}"
    end
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
