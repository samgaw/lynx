defmodule Lynx.Rust.ResultModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants, LLBC}

  # Aeneas's map_err model invokes the actual FnOnce implementation, but does
  # not drop an unused callback on Ok. Admit only capture-free compiler closures
  # with NoopDestruct; captured state and user-written FnOnce implementations
  # require an explicit destructor model instead.
  def resolve(
        %{
          "body" => "Opaque",
          "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["result", 0]},
              %{"Impl" => %{"Ty" => %{"skip_binder" => parent, "params" => parent_params}}},
              %{"Ident" => ["map_err", 0]}
            ]
          },
          "generics" => generics
        },
        translated,
        refs
      ) do
    expand = &CallModels.expand(&1, refs)

    with [input, callback] <- Enum.map(sig["inputs"], expand),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- input,
         true <- LLBC.result_type?(id, %{translated: translated, references: refs}),
         true <- args == arguments([variable(0), variable(1)]),
         true <- expand.(parent) |> free_parent() == input,
         true <- parameters?(parent_params, 2),
         true <- callback == variable(3),
         true <-
           expand.(sig["output"]) ==
             put_in(input, ["Adt", "generics"], arguments([variable(0), variable(2)])),
         %{"trait_clauses" => [fn_once, destruct]} <- generics,
         true <- parameters?(%{generics | "trait_clauses" => []}, 4),
         {0, fn_once_id, [functor, tuple, output]} <- clause(fn_once, refs),
         true <- functor == variable(3) and output == variable(2),
         true <- tuple?(tuple, [variable(1)]),
         true <- trait?(translated, fn_once_id, ~w(core ops function FnOnce), 3),
         {1, destruct_id, [destruct_type]} <- clause(destruct, refs),
         true <- destruct_type == variable(3),
         true <- trait?(translated, destruct_id, ~w(core marker Destruct), 1) do
      %{
        rust_name: "core::result::{core::result::Result<@T, @E>}::map_err",
        lean: "Aeneas.Std.core.result.Result.map_err",
        builtin: true,
        can_fail: true,
        lift: false,
        callback: :capture_free,
        fn_once_trait: fn_once_id,
        destruct_trait: destruct_id,
        label:
          "Aeneas Result::map_err with an extracted capture-free FnOnce callback and validated NoopDestruct; Rust core implementation not verified"
      }
    else
      _ -> nil
    end
  end

  def resolve(_, _, _), do: nil

  def audit(functions, models, translated, refs) do
    context = %{
      models: models,
      translated: translated,
      refs: refs,
      traits: trait_references(translated, %{}),
      functions: Map.new(functions, &{&1["def_id"], &1})
    }

    Enum.reduce_while(functions, {:ok, %{}}, fn function, {:ok, dependencies} ->
      try do
        ids = callbacks(function["body"], context) |> Enum.uniq() |> Enum.sort()
        {:cont, {:ok, Map.put(dependencies, function["def_id"], ids)}}
      rescue
        error in ArgumentError -> {:halt, {:error, function, Exception.message(error)}}
      end
    end)
  end

  defp callbacks(
         %{
           "Call" => %{
             "call" => %{
               "func" => %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}
             }
           }
         } = node,
         context
       ) do
    direct =
      case context.models[id] do
        %{callback: :capture_free} = model -> [callback!(args, model, context)]
        _ -> []
      end

    direct ++ Enum.flat_map(Map.values(node), &callbacks(&1, context))
  end

  defp callbacks(node, context) when is_map(node),
    do: Enum.flat_map(Map.values(node), &callbacks(&1, context))

  defp callbacks(nodes, context) when is_list(nodes),
    do: Enum.flat_map(nodes, &callbacks(&1, context))

  defp callbacks(_, _), do: []

  defp callback!(args, model, ctx) do
    expand = &CallModels.expand(&1, ctx.refs)

    with %{
           "regions" => [],
           "const_generics" => [],
           "types" => [_, error, output, closure],
           "trait_refs" => [fn_ref, drop_ref]
         } <- args,
         %{"Adt" => %{"id" => type_id, "builtin" => nil, "generics" => type_args}} = closure_type <-
           expand.(closure),
         true <- Constants.empty_arguments?(type_args),
         %{
           "kind" => %{"Struct" => []},
           "generics" => params,
           "item_meta" => %{"opacity" => "Transparent"},
           "src" => %{"Closure" => %{"info" => info}}
         } <- declaration(ctx.translated["type_decls"], type_id),
         true <- parameters?(params, 0),
         %{
           "kind" => "FnOnce",
           "closure_body" => %{"id" => body_id, "generics" => body_args},
           "fn_once_impl" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => impl_id, "generics" => impl_args}
           }
         } <- info,
         true <- Constants.empty_arguments?(body_args) and Constants.empty_arguments?(impl_args),
         %{
           "kind" => %{"TraitImpl" => %{"id" => ^impl_id, "generics" => ref_args}},
           "trait_decl_ref" => fn_decl
         } <- reference(fn_ref, ctx.traits),
         true <- Constants.empty_arguments?(ref_args),
         true <- fn_decl["id"] == model.fn_once_trait,
         [dict_closure, dict_tuple, dict_output] <- expand.(fn_decl["generics"])["types"],
         true <- dict_closure == closure_type and dict_output == expand.(output),
         true <- tuple?(dict_tuple, [expand.(error)]),
         %{
           "kind" => %{
             "BuiltinOrAuto" => %{
               "builtin_data" => "NoopDestruct",
               "parent_trait_refs" => [],
               "types" => [],
               "vtable" => nil
             }
           },
           "trait_decl_ref" => drop_decl
         } <- reference(drop_ref, ctx.traits),
         true <- drop_decl["id"] == model.destruct_trait,
         true <- expand.(drop_decl["generics"]) == arguments([closure_type]),
         %{
           "signature" => %{
             "is_unsafe" => false,
             "abi" => %{"Other" => "rust-call"},
             "is_variadic" => false,
             "inputs" => inputs,
             "output" => result
           },
           "src" => %{
             "TraitImpl" => %{
               "impl_ref" => %{"id" => ^impl_id},
               "trait_ref" => trait_ref,
               "item_id" => 0,
               "reuses_default" => false
             }
           }
         } <- ctx.functions[body_id],
         true <- parameters?(get_in(ctx.functions, [body_id, "generics"]), 0),
         true <- Enum.map(inputs, expand) == [closure_type, dict_tuple],
         true <- expand.(result) == expand.(output),
         true <- trait_ref["id"] == model.fn_once_trait,
         true <-
           expand.(trait_ref["generics"]) ==
             arguments([closure_type, dict_tuple, expand.(output)]),
         %{
           "src" => %{"Closure" => %{"kind" => "FnOnce"}},
           "is_negative" => false,
           "is_unsafe" => false,
           "generics" => impl_params,
           "impl_trait" => impl_trait,
           "methods" => [method]
         } <- declaration(ctx.translated["trait_impls"], impl_id),
         true <- parameters?(impl_params, 0),
         true <- impl_trait["id"] == model.fn_once_trait,
         true <-
           expand.(impl_trait["generics"]) ==
             arguments([closure_type, dict_tuple, expand.(output)]),
         %{
           "params" => method_params,
           "skip_binder" => %{"id" => ^body_id, "generics" => method_args},
           "kind" => %{"TraitMethod" => [trait_id, 0]}
         } <- method,
         true <-
           trait_id == model.fn_once_trait and parameters?(method_params, 0) and
             Constants.empty_arguments?(method_args) do
      body_id
    else
      _ ->
        raise ArgumentError,
              "Result::map_err requires an extracted capture-free compiler FnOnce callback with matching signature, implementation identity and NoopDestruct"
    end
  end

  defp reference(%{"regions" => [], "outlives" => [], "skip_binder" => value}, refs) do
    case value do
      %{"Value" => [_, value]} -> value
      %{"Deduplicated" => id} -> Map.get(refs, id)
      _ -> nil
    end
  end

  defp reference(_, _), do: nil

  # Trait-reference and type hash-cons IDs occupy different namespaces.
  defp trait_references(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = ref]}, refs) do
    if Map.has_key?(refs, id) and refs[id] != ref,
      do: raise(ArgumentError, "inconsistent LLBC shared trait identity")

    trait_references(ref, Map.put(refs, id, ref))
  end

  defp trait_references(value, refs) when is_map(value),
    do: Enum.reduce(Map.values(value), refs, &trait_references/2)

  defp trait_references(values, refs) when is_list(values),
    do: Enum.reduce(values, refs, &trait_references/2)

  defp trait_references(_, refs), do: refs

  defp clause(
         %{
           "clause_id" => index,
           "trait_" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => id, "generics" => args}
           }
         },
         refs
       ) do
    case CallModels.expand(args, refs) do
      %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []} ->
        {index, id, types}

      _ ->
        nil
    end
  end

  defp clause(_, _), do: nil

  defp trait?(translated, id, path, count) do
    case declaration(translated["trait_decls"], id) do
      %{"item_meta" => %{"name" => name}, "generics" => params} ->
        name == Enum.map(path, &%{"Ident" => [&1, 0]}) and parameters?(params, count)

      _ ->
        false
    end
  end

  defp parameters?(
         %{
           "regions" => [],
           "types" => types,
           "const_generics" => [],
           "trait_clauses" => [],
           "outlives" => [],
           "trait_type_constraints" => []
         },
         count
       ) do
    expected = if count == 0, do: [], else: Enum.to_list(0..(count - 1))
    Enum.map(types, & &1["index"]) == expected
  end

  defp parameters?(_, _), do: false

  defp tuple?(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}, types),
    do: args == arguments(types)

  defp tuple?(_, _), do: false
  defp variable(index), do: %{"TypeVar" => %{"Free" => index}}

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp declaration(values, id), do: Enum.find(values || [], &(&1 && &1["def_id"] == id))
  defp free_parent(%{"Bound" => [0, index]}), do: %{"Free" => index}

  defp free_parent(value) when is_map(value),
    do: Map.new(value, fn {k, v} -> {k, free_parent(v)} end)

  defp free_parent(value) when is_list(value), do: Enum.map(value, &free_parent/1)
  defp free_parent(value), do: value
end
