defmodule Lynx.Rust.FormatModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants, LLBC}

  # The bounded runtime is not permission to use arbitrary formatting operations.
  # Start with default ToString and write_str, checking the nominal types and
  # actual Display dictionary. Debug, options and custom writers stay closed.
  def resolve(function, translated, refs) do
    ctx = %{translated: translated, refs: refs}

    with %{
           "body" => "Opaque",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"},
           "item_meta" => %{"name" => name}
         } <- function do
      case name do
        [
          %{"Ident" => ["alloc", 0]},
          %{"Ident" => ["string", 0]},
          %{"Impl" => %{"Trait" => impl}},
          %{"Ident" => ["to_string", 0]}
        ] ->
          to_string_model(function, impl, ctx)

        [
          %{"Ident" => ["core", 0]},
          %{"Ident" => ["fmt", 0]},
          %{"Impl" => %{"Ty" => %{"skip_binder" => parent, "params" => params}}},
          %{"Ident" => ["write_str", 0]}
        ] ->
          write_str_model(function, parent, params, ctx)

        _ ->
          nil
      end
    else
      _ -> nil
    end
  end

  defp to_string_model(function, impl_id, ctx) do
    ctx = Map.put(ctx, :traits, trait_references(ctx.translated, %{}))
    sig = expand(function["signature"], ctx)
    generics = expand(function["generics"], ctx)

    with true <- parameters?(generics, 1, 1),
         %{"trait_clauses" => [clause]} <- generics,
         {:ok, display} <- display_clause(clause, ctx),
         true <- generics["outlives"] == [outlives(%{"Lub" => variable(0)}, region(0))],
         true <- sig["inputs"] == [reference(region(0), variable(0), "Shared")],
         true <- named_type?(sig["output"], ~w(alloc string String), [], ctx),
         %{
           "is_negative" => false,
           "is_unsafe" => false,
           "src" => "Normal",
           "generics" => impl_params,
           "impl_trait" => %{"id" => to_string, "generics" => impl_trait_args}
         } = impl <- declaration(ctx, "trait_impls", impl_id),
         true <- parameters?(impl_params, 0, 1),
         [impl_clause] <- impl_params["trait_clauses"],
         {:ok, ^display} <- display_clause(impl_clause, ctx),
         true <- impl_params["outlives"] == [],
         true <- expand(impl_trait_args, ctx) == arguments([variable(0)]),
         true <- to_string_trait?(to_string, ctx),
         true <- method_identity?(function, impl, to_string, ctx) do
      model(
        "alloc::string::{alloc::string::ToString<@T>}::to_string",
        "Aeneas.Std.alloc.string.ToString.to_string",
        false,
        "Bounded default ToString model invoking the actual audited Display method; allocation success assumed; Rust alloc implementation not verified"
      )
      |> Map.put(:display_trait, display)
    else
      _ -> nil
    end
  end

  defp write_str_model(function, parent, params, ctx) do
    sig = expand(function["signature"], ctx)
    generics = expand(function["generics"], ctx)
    parent = parent |> expand(ctx) |> free_bound()

    with true <- plain_parameters?(params, 1, 0),
         true <- named_type?(parent, ~w(core fmt Formatter), [region(0)], ctx),
         true <- plain_parameters?(generics, 3, 0, [outlives(region(0), region(1))]),
         [writer, text] <- sig["inputs"],
         true <- writer == reference(region(1), parent, "Mut"),
         %{"Ref" => [text_region, string, "Shared"]} <- text,
         true <- text_region == region(2),
         true <- str_type?(string),
         true <- fmt_result?(sig["output"], ctx) do
      model(
        "core::fmt::{core::fmt::Formatter<'a>}::write_str",
        "Aeneas.Std.core.fmt.Formatter.write_str",
        true,
        "Bounded default UTF-8 string writer model; allocation success assumed; unsupported size is a verification cutoff; Rust core implementation not verified"
      )
    else
      _ -> nil
    end
  end

  def audit(functions, models, translated, refs) do
    ctx = %{
      translated: translated,
      refs: refs,
      models: models,
      traits: trait_references(translated, %{}),
      functions: Map.new(functions, &{&1["def_id"], &1})
    }

    Enum.reduce_while(functions, {:ok, %{}}, fn function, {:ok, dependencies} ->
      try do
        ids = dispatches(function["body"], ctx) |> Enum.uniq() |> Enum.sort()
        {:cont, {:ok, Map.put(dependencies, function["def_id"], ids)}}
      rescue
        error in ArgumentError -> {:halt, {:error, function, Exception.message(error)}}
      end
    end)
  end

  defp dispatches(
         %{
           "Call" => %{
             "call" => %{
               "func" => %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}
             }
           }
         } = node,
         ctx
       ) do
    direct =
      case ctx.models[id] do
        %{display_trait: trait} -> [display_method!(args, trait, ctx)]
        _ -> []
      end

    direct ++ Enum.flat_map(Map.values(node), &dispatches(&1, ctx))
  end

  defp dispatches(node, ctx) when is_map(node),
    do: Enum.flat_map(Map.values(node), &dispatches(&1, ctx))

  defp dispatches(nodes, ctx) when is_list(nodes), do: Enum.flat_map(nodes, &dispatches(&1, ctx))
  defp dispatches(_, _), do: []

  # Initially accept monomorphic Display implementations only. In particular,
  # this does not silently use Aeneas builtin renderers found via dictionaries.
  defp display_method!(args, trait, ctx) do
    with %{"regions" => [_], "types" => [self], "const_generics" => [], "trait_refs" => [ref]} <-
           args,
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => impl_args}},
           "trait_decl_ref" => %{"id" => ^trait, "generics" => trait_args}
         } <- trait_reference(ref, ctx.traits),
         true <- Constants.empty_arguments?(impl_args),
         true <- expand(trait_args, ctx) == arguments([expand(self, ctx)]),
         %{
           "is_negative" => false,
           "is_unsafe" => false,
           "src" => "Normal",
           "generics" => params,
           "impl_trait" => impl_trait,
           "consts" => [],
           "types" => [],
           "implied_trait_refs" => [],
           "methods" => [%{"skip_binder" => %{"id" => method_id}}]
         } = impl <- declaration(ctx, "trait_impls", impl_id),
         true <- plain_parameters?(params, 0, 0),
         true <-
           expand(impl_trait, ctx) == %{"id" => trait, "generics" => expand(trait_args, ctx)},
         %{} = function <- ctx.functions[method_id],
         true <- method_identity?(function, impl, trait, ctx),
         true <- display_signature?(function, expand(self, ctx), ctx) do
      method_id
    else
      _ ->
        raise ArgumentError,
              "ToString requires a monomorphic extracted Display implementation with matching dictionary type, method identity and signature; external renderers are not implicitly approved"
    end
  end

  defp method_identity?(function, impl, trait, ctx) do
    id = function["def_id"]
    impl_id = impl["def_id"]

    with %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => ^impl_id},
             "trait_ref" => %{"id" => ^trait},
             "item_id" => 0,
             "reuses_default" => false
           }
         } <- function["src"],
         [
           %{
             "kind" => %{"TraitMethod" => [^trait, 0]},
             "params" => params,
             "skip_binder" => %{"id" => ^id, "generics" => args}
           }
         ] <- impl["methods"],
         true <-
           plain_parameters?(
             params,
             length(function["generics"]["regions"]) - length(impl["generics"]["regions"]),
             0
           ),
         true <- generic_arguments?(args, impl, ctx, :method, function) do
      # The method's source must refer to the same impl and trait, including Self.
      source = function["src"]["TraitImpl"]

      expand(source["trait_ref"], ctx) == expand(impl["impl_trait"], ctx) and
        generic_arguments?(source["impl_ref"]["generics"], impl, ctx, :impl, function)
    else
      _ -> false
    end
  end

  defp generic_arguments?(args, impl, ctx, kind, function) do
    n = length(function["generics"]["regions"]) - length(impl["generics"]["regions"])

    regions =
      if kind == :method, do: Enum.map(indices(n), &%{"Var" => %{"Bound" => [0, &1]}}), else: []

    expected =
      arguments(Enum.map(impl["generics"]["types"], &variable(&1["index"])))
      |> Map.put("regions", regions)

    clauses = impl["generics"]["trait_clauses"]
    refs = args["trait_refs"]

    expand(Map.put(args, "trait_refs", []), ctx) == expected and is_list(refs) and
      length(refs) == length(clauses) and
      Enum.all?(Enum.zip(refs, clauses), fn {ref, clause} ->
        case trait_reference(ref, ctx.traits) do
          %{
            "kind" => %{"Clause" => [%{"Free" => index}, %{"regions" => []}]},
            "trait_decl_ref" => decl
          } ->
            index == clause["clause_id"] and
              expand(decl, ctx) == expand(clause["trait_"]["skip_binder"], ctx)

          _ ->
            false
        end
      end)
  end

  defp display_signature?(function, self, ctx) do
    sig = expand(function["signature"], ctx)
    params = expand(function["generics"], ctx)
    expected = [outlives(region(2), region(1))]

    with true <- plain_parameters?(params, 3, 0, params["outlives"]),
         true <- params["outlives"] in [[], expected],
         %{
           "is_unsafe" => false,
           "is_variadic" => false,
           "abi" => "Rust",
           "inputs" => [input, writer]
         } <- sig,
         true <- input == reference(region(0), self, "Shared"),
         %{"Ref" => [writer_region, formatter, "Mut"]} <- writer,
         true <- writer_region == region(1),
         true <- named_type?(formatter, ~w(core fmt Formatter), [region(2)], ctx) do
      fmt_result?(sig["output"], ctx)
    else
      _ -> false
    end
  end

  defp display_clause(
         %{
           "clause_id" => 0,
           "trait_" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => id, "generics" => args}
           }
         },
         ctx
       ) do
    if expand(args, ctx) == arguments([variable(0)]) and display_trait?(id, ctx),
      do: {:ok, id},
      else: :error
  end

  defp display_clause(_, _), do: :error

  defp display_trait?(id, ctx) do
    case declaration(ctx, "trait_decls", id) do
      %{
        "item_meta" => %{"name" => name},
        "is_unsafe" => false,
        "generics" => params,
        "consts" => [],
        "types" => [],
        "implied_clauses" => [],
        "methods" => [
          %{
            "kind" => %{"TraitMethod" => [^id, 0]},
            "params" => method_params,
            "skip_binder" => %{"name" => "fmt", "signature" => sig, "default" => nil}
          }
        ]
      } ->
        name == path(~w(core fmt Display)) and plain_parameters?(params, 0, 1) and
          plain_parameters?(method_params, 3, 0) and
          display_signature?(
            %{"signature" => sig |> expand(ctx) |> free_bound(), "generics" => method_params(3)},
            variable(0),
            ctx
          )

      _ ->
        false
    end
  end

  defp to_string_trait?(id, ctx) do
    case declaration(ctx, "trait_decls", id) do
      %{
        "item_meta" => %{"name" => name},
        "is_unsafe" => false,
        "generics" => params,
        "consts" => [],
        "types" => [],
        "implied_clauses" => [],
        "methods" => [
          %{
            "kind" => %{"TraitMethod" => [^id, 0]},
            "params" => method_params,
            "skip_binder" => %{"name" => "to_string", "signature" => sig, "default" => nil}
          }
        ]
      } ->
        sig = sig |> expand(ctx) |> free_bound()

        name == path(~w(alloc string ToString)) and plain_parameters?(params, 0, 1) and
          plain_parameters?(method_params, 1, 0) and
          sig["is_unsafe"] == false and sig["abi"] == "Rust" and sig["is_variadic"] == false and
          sig["inputs"] == [reference(region(0), variable(0), "Shared")] and
          named_type?(sig["output"], ~w(alloc string String), [], ctx)

      _ ->
        false
    end
  end

  defp fmt_result?(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}}, ctx) do
    case args do
      %{"regions" => [], "const_generics" => [], "trait_refs" => [], "types" => [unit, error]} ->
        LLBC.result_type?(id, %{translated: ctx.translated, references: ctx.refs}) and
          match?(
            %{
              "Adt" => %{
                "builtin" => "Tuple",
                "generics" => %{
                  "regions" => [],
                  "types" => [],
                  "const_generics" => [],
                  "trait_refs" => []
                }
              }
            },
            unit
          ) and
          named_type?(error, ~w(core fmt Error), [], ctx)

      _ ->
        false
    end
  end

  defp fmt_result?(_, _), do: false

  defp named_type?(
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}},
         name,
         regions,
         ctx
       ) do
    case declaration(ctx, "type_decls", id) do
      %{"item_meta" => %{"name" => actual}, "kind" => kind, "generics" => params} ->
        bounds = if name == ~w(core fmt Formatter), do: [outlives(region(0), region(0))], else: []
        expected_kind = if name == ~w(core fmt Error), do: %{"Struct" => []}, else: "Opaque"

        actual == path(name) and args == Map.put(arguments([]), "regions", regions) and
          kind == expected_kind and
          plain_parameters?(params, length(regions), 0, bounds)

      _ ->
        false
    end
  end

  defp named_type?(_, _, _, _), do: false

  defp str_type?(%{"Adt" => %{"builtin" => "Str", "generics" => args}}),
    do: Constants.empty_arguments?(args)

  defp str_type?(_), do: false

  defp parameters?(
         %{
           "regions" => regions,
           "types" => types,
           "const_generics" => [],
           "trait_type_constraints" => []
         },
         nr,
         nt
       )
       when is_list(regions) and is_list(types),
       do:
         Enum.map(regions, & &1["index"]) == indices(nr) and
           Enum.map(types, & &1["index"]) == indices(nt)

  defp parameters?(_, _, _), do: false

  defp plain_parameters?(params, nr, nt, outlives \\ []),
    do:
      parameters?(params, nr, nt) and params["trait_clauses"] == [] and
        params["outlives"] == outlives

  defp method_params(n),
    do: %{
      "regions" => Enum.map(indices(n), &%{"index" => &1}),
      "types" => [],
      "const_generics" => [],
      "trait_clauses" => [],
      "outlives" => [],
      "trait_type_constraints" => []
    }

  defp indices(0), do: []
  defp indices(n) when n > 0, do: Enum.to_list(0..(n - 1))
  defp variable(i), do: %{"TypeVar" => %{"Free" => i}}
  defp region(i), do: %{"Var" => %{"Free" => i}}
  defp reference(r, t, kind), do: %{"Ref" => [r, t, kind]}

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp outlives(left, right),
    do: %{"regions" => [], "outlives" => [], "skip_binder" => [left, right]}

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp model(rust, lean, builtin, label),
    do: %{
      rust_name: rust,
      lean: lean,
      builtin: builtin,
      can_fail: true,
      lift: false,
      label: label
    }

  defp expand(value, ctx), do: CallModels.expand(value, ctx.refs)

  defp declaration(ctx, key, id),
    do: Enum.find(ctx.translated[key] || [], &(&1 && &1["def_id"] == id))

  # These method binders introduce regions, not additional type parameters.
  defp free_bound(%{"Var" => %{"Bound" => [0, i]}}), do: region(i)
  defp free_bound(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free_bound(v)} end)
  defp free_bound(list) when is_list(list), do: Enum.map(list, &free_bound/1)
  defp free_bound(value), do: value

  defp trait_reference(
         %{"regions" => [], "outlives" => [], "skip_binder" => %{"Value" => [_, value]}},
         _
       ),
       do: value

  defp trait_reference(
         %{"regions" => [], "outlives" => [], "skip_binder" => %{"Deduplicated" => id}},
         refs
       ),
       do: refs[id]

  defp trait_reference(_, _), do: nil

  defp trait_references(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = ref]}, refs) do
    if Map.has_key?(refs, id) and refs[id] != ref,
      do: raise(ArgumentError, "inconsistent LLBC shared trait identity")

    trait_references(ref, Map.put(refs, id, ref))
  end

  defp trait_references(map, refs) when is_map(map),
    do: Enum.reduce(Map.values(map), refs, &trait_references/2)

  defp trait_references(list, refs) when is_list(list),
    do: Enum.reduce(list, refs, &trait_references/2)

  defp trait_references(_, refs), do: refs
end
