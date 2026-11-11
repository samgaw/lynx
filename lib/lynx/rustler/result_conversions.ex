defmodule Lynx.Rustler.ResultConversions do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, OptionModels}
  @empty %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  # These consuming operations are specialized to the identified SDK Error.
  # Their discarded errors use the existing partial destruction model, never
  # the generic upstream operation which can erase an observable destructor.
  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => [family, 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent_params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => [method, 0]}
             ]
           },
           "generics" => params
         } <- function,
         true <- {family, method} in [{"option", "ok_or"}, {"result", "ok"}],
         %{"kind" => "Opaque", "def_id" => error} <-
           named(translated["type_decls"], ~w(rustler error Error)),
         %{"def_id" => option} = option_type <-
           named(translated["type_decls"], ~w(core option Option)),
         true <- OptionModels.option_type?(option_type, refs),
         %{"def_id" => result} <- named(translated["type_decls"], ~w(core result Result)),
         true <- LLBC.result_type?(result, %{translated: translated, references: refs}),
         true <- parameters?(parent_params, if(family == "option", do: 1, else: 2)),
         %{"trait_clauses" => clauses} <- params,
         true <- parameters?(%{params | "trait_clauses" => []}, 2),
         expected_variables =
           if(method == "ok_or", do: [variable(1)], else: [variable(0), variable(1)]),
         [{0, destruct, _} | _] = actual_clauses <- Enum.map(clauses, &clause(&1, refs)),
         true <-
           actual_clauses ==
             Enum.with_index(expected_variables)
             |> Enum.map(fn {type, index} -> {index, destruct, [type]} end),
         true <- destruct?(translated, destruct),
         expected = signature(method, option, result),
         true <- CallModels.expand(sig, refs) == expected,
         expected_parent =
           if(family == "option",
             do: adt(option, [bound(0)]),
             else: adt(result, [bound(0), bound(1)])
           ),
         true <- CallModels.expand(parent, refs) == expected_parent do
      %{
        rust_name:
          if(method == "ok_or",
            do: "core::option::{core::option::Option<@T>}::ok_or",
            else: "core::result::{core::result::Result<@T, @E>}::ok"
          ),
        backend_rust_name: "lynx_rustler::" <> method,
        lean:
          "Lynx.Rustler.Decoding." <> if(method == "ok_or", do: "optionOkOr", else: "resultOk"),
        builtin: false,
        can_fail: true,
        lift: false,
        keep_params: [true, false],
        conversion_destruct_trait: destruct,
        conversion_destruct_variables: if(method == "ok_or", do: [1], else: [0, 1]),
        model_hash: Lynx.Rustler.Bridge.fingerprint(),
        rustler_result_conversion: method,
        rustler_error_type: error,
        label:
          "Consuming #{family}::#{method} specialized to validated Rustler Error: discarded static/scalar SDK errors use partial cleanup; boxed errors exhaust verification; Rust core, SDK, allocator and native FFI unverified"
      }
    else
      _ -> nil
    end
  end

  def audit(functions, models, translated, refs) do
    refs = %{types: refs, traits: trait_references(translated, %{}), translated: translated}

    Enum.reduce_while(functions, :ok, fn function, :ok ->
      case valid_calls?(function["body"], models, refs) do
        true ->
          {:cont, :ok}

        false ->
          {:halt,
           {:error, function,
            "consuming Option/Result conversion requires the actual Rustler Error type and concrete compiler Destruct dictionaries"}}
      end
    end)
  end

  defp valid_calls?(
         %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}} = node,
         models,
         refs
       ) do
    case models[id] do
      %{rustler_result_conversion: _, rustler_error_type: error} = model ->
        match?(
          %{"regions" => [], "types" => [_, _], "const_generics" => [], "trait_refs" => _},
          args
        ) and
          is_list(args["trait_refs"]) and
          length(args["trait_refs"]) == length(model.conversion_destruct_variables) and
          CallModels.expand(Enum.at(args["types"], 1), refs.types) == adt(error, []) and
          Enum.all?(Enum.zip(args["trait_refs"], model.conversion_destruct_variables), fn {dict,
                                                                                           index} ->
            destruction_dictionary?(
              dict,
              model.conversion_destruct_trait,
              Enum.at(args["types"], index),
              refs
            )
          end)

      _ ->
        valid_calls?(Map.values(node), models, refs)
    end
  end

  defp valid_calls?(map, models, refs) when is_map(map),
    do: valid_calls?(Map.values(map), models, refs)

  defp valid_calls?(list, models, refs) when is_list(list),
    do: Enum.all?(list, &valid_calls?(&1, models, refs))

  defp valid_calls?(_, _, _), do: true

  defp destruction_dictionary?(
         %{"regions" => [], "outlives" => [], "skip_binder" => dict},
         id,
         type,
         refs
       ) do
    dict =
      case dict do
        %{"Value" => [_, value]} -> value
        %{"Deduplicated" => key} -> refs.traits[key]
        value -> value
      end

    expected = %{@empty | "types" => [CallModels.expand(type, refs.types)]}

    with %{"kind" => kind, "trait_decl_ref" => %{"id" => ^id, "generics" => args}} <- dict,
         true <- CallModels.expand(args, refs.types) == expected do
      case kind do
        %{
          "BuiltinOrAuto" => %{
            "builtin_data" => "NoopDestruct",
            "parent_trait_refs" => [],
            "types" => [],
            "vtable" => nil
          }
        } ->
          true

        %{"TraitImpl" => %{"id" => impl, "generics" => @empty}} ->
          case Enum.find(refs.translated["trait_impls"], &(&1 && &1["def_id"] == impl)) do
            %{
              "src" => "Destruct",
              "is_unsafe" => false,
              "is_negative" => false,
              "impl_trait" => trait,
              "generics" => params
            } ->
              parameters?(params, 0) and
                CallModels.expand(trait, refs.types) == %{"id" => id, "generics" => expected}

            _ ->
              false
          end

        _ ->
          false
      end
    else
      _ -> false
    end
  end

  defp destruction_dictionary?(_, _, _, _), do: false

  defp trait_references(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = ref]}, acc) do
    if Map.has_key?(acc, id) and acc[id] != ref,
      do: raise(ArgumentError, "inconsistent compiler trait identity")

    trait_references(ref, Map.put(acc, id, ref))
  end

  defp trait_references(map, acc) when is_map(map), do: trait_references(Map.values(map), acc)

  defp trait_references(list, acc) when is_list(list),
    do: Enum.reduce(list, acc, &trait_references/2)

  defp trait_references(_, acc), do: acc

  defp signature(method, option, result) do
    t = variable(0)
    e = variable(1)

    {inputs, output} =
      if method == "ok_or",
        do: {[adt(option, [t]), e], adt(result, [t, e])},
        else: {[adt(result, [t, e])], adt(option, [t])}

    %{
      "abi" => "Rust",
      "is_unsafe" => false,
      "is_variadic" => false,
      "inputs" => inputs,
      "output" => output
    }
  end

  defp clause(
         %{
           "clause_id" => index,
           "trait_" => %{"regions" => [], "outlives" => [], "skip_binder" => trait}
         },
         refs
       ) do
    case CallModels.expand(trait, refs) do
      %{
        "id" => id,
        "generics" => %{
          "regions" => [],
          "types" => types,
          "const_generics" => [],
          "trait_refs" => []
        }
      } ->
        {index, id, types}

      _ ->
        nil
    end
  end

  defp clause(_, _), do: nil

  defp destruct?(translated, id) do
    case Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == id)) do
      %{
        "item_meta" => %{"name" => name},
        "is_unsafe" => false,
        "methods" => methods,
        "generics" => params
      } ->
        name == path(~w(core marker Destruct)) and parameters?(params, 1) and
          Enum.all?(methods, &(get_in(&1, ["skip_binder", "name"]) == "drop_glue"))

      _ ->
        false
    end
  end

  defp parameters?(params, count) do
    is_map(params) and
      Enum.map(params["types"], & &1["index"]) ==
        if(count == 0, do: [], else: Enum.to_list(0..(count - 1))) and
      Enum.all?(
        ~w(regions const_generics trait_clauses outlives trait_type_constraints),
        &(params[&1] == [])
      )
  end

  defp adt(id, types),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => %{@empty | "types" => types}}}

  defp variable(n), do: %{"TypeVar" => %{"Free" => n}}
  defp bound(n), do: %{"TypeVar" => %{"Bound" => [0, n]}}
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp named(values, parts),
    do: Enum.find(values, &(&1 && &1["item_meta"]["name"] == path(parts)))
end
