defmodule Lynx.Rustler.EncoderModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants, FormatModels}

  def resolve(
        %{
          "body" => "Opaque",
          "src" => "Normal",
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["rustler", 0]},
              %{"Ident" => ["types", 0]},
              %{"Ident" => ["tuple", 0]},
              %{"Ident" => ["make_tuple", 0]}
            ]
          }
        } = function,
        translated,
        refs
      ) do
    ctx = context(translated, refs)
    params = expand(function["generics"], ctx)
    signature = expand(function["signature"], ctx)

    with %{"Adt" => _} = env <- named(ctx, ~w(rustler env Env), [region(0)], []),
         %{"Adt" => _} = input_term <- named(ctx, ~w(rustler term Term), [region(2)], []),
         %{"Adt" => _} = output_term <- named(ctx, ~w(rustler term Term), [region(0)], []),
         true <- Enum.map(params["regions"], & &1["index"]) == [0, 1, 2],
         true <-
           params["types"] == [] and params["const_generics"] == [] and
             params["trait_clauses"] == [] and params["trait_type_constraints"] == [],
         true <- params["outlives"] == [outlives(region(2), region(1))],
         true <-
           signature["abi"] == "Rust" and signature["is_unsafe"] == false and
             signature["is_variadic"] == false,
         true <-
           signature["inputs"] == [env, reference(region(1), %{"Slice" => [input_term, nil]})],
         true <- signature["output"] == output_term do
      %{
        rust_name: "rustler::types::tuple::make_tuple",
        lean: "Lynx.Rustler.Encoding.makeTuple",
        builtin: false,
        can_fail: true,
        lift: false,
        label:
          "Rustler tuple construction FFI model: ordered term slice and 16777215-field verification limit; native environment, handles, allocation and Rustler implementation unverified"
      }
    else
      _ -> nil
    end
  end

  def resolve(
        %{
          "body" => "Opaque",
          "item_meta" => %{
            "name" =>
              [
                %{"Ident" => ["rustler", 0]},
                %{"Ident" => ["types", 0]} | _
              ] = name
          }
        } = function,
        translated,
        refs
      ) do
    ctx = context(translated, refs)

    with [%{"Ident" => ["rustler", 0]}, %{"Ident" => ["types", 0]} | rest] <- name,
         [%{"Ident" => ["encode", 0]}, %{"Impl" => %{"Trait" => impl_id}} | scope] <-
           Enum.reverse(rest),
         %{} = impl <- declaration(ctx, "trait_impls", impl_id),
         %{"id" => trait, "generics" => %{"types" => [self]}} <- impl["impl_trait"],
         true <- trait?(trait, ctx),
         true <- FormatModels.method_identity?(function, impl, trait, ctx),
         true <-
           impl["src"] == "Normal" and impl["is_negative"] == false and impl["is_unsafe"] == false,
         true <- impl["consts"] == [] and impl["types"] == [] and impl["implied_trait_refs"] == [],
         self = expand(self, ctx),
         true <-
           expand(impl["impl_trait"], ctx) == %{"id" => trait, "generics" => arguments([self])},
         {kind, rust_self, count, inherited} <- shape(Enum.reverse(scope), self, ctx),
         true <- signature?(function, self, inherited, ctx),
         true <- parameters?(function["generics"], inherited + 2, count, trait, ctx),
         true <- parameters?(impl["generics"], inherited, count, trait, ctx),
         true <- outlives?(kind, function["generics"], impl["generics"], count, ctx) do
      %{
        rust_name:
          "rustler::types" <>
            Enum.map_join(Enum.reverse(scope), "", fn %{"Ident" => [part, 0]} -> "::" <> part end) <>
            "::{rustler::types::Encoder<" <> rust_self <> ">}::encode",
        lean: "Lynx.Rustler.Encoding." <> kind,
        builtin: false,
        can_fail: true,
        lift: false,
        encoder_trait: trait,
        encoder_slots: count,
        encoder_regions: inherited + 2,
        encoder_standard: true,
        label:
          "Stateless Rustler Encoder FFI model invoking audited nested encoders; native handles and allocation success assumed; Rustler implementation not verified" <>
            if(kind == "vec",
              do:
                "; 2147483647-element verification limit preserves OTP unsigned allocation-count arithmetic",
              else: ""
            )
      }
    else
      _ -> nil
    end
  end

  def resolve(_, _, _), do: nil

  def binding!(type_id, audit, translation) do
    ctx = context(audit.translated, audit.references)
    self = %{"Adt" => %{"id" => type_id, "builtin" => nil, "generics" => arguments([])}}

    candidates =
      Enum.filter(audit.functions, fn function ->
        with %{
               "TraitImpl" => %{"impl_ref" => %{"id" => impl_id}, "trait_ref" => %{"id" => trait}}
             } <- function["src"],
             %{} = impl <- declaration(ctx, "trait_impls", impl_id) do
          trait?(trait, ctx) and
            impl["src"] == "Normal" and impl["is_negative"] == false and
            impl["is_unsafe"] == false and
            impl["consts"] == [] and impl["types"] == [] and impl["implied_trait_refs"] == [] and
            expand(impl["impl_trait"], ctx) == %{"id" => trait, "generics" => arguments([self])} and
            Enum.all?(Map.values(impl["generics"]), &(&1 == [])) and
            parameters?(function["generics"], 2, 0, trait, ctx) and
            function["generics"]["outlives"] == [] and
            signature?(function, self, 0, ctx) and
            FormatModels.method_identity?(function, impl, trait, ctx)
        else
          _ -> false
        end
      end)

    with [function] <- candidates,
         [%{"is_opaque" => false, "lean_name" => encoder}] <-
           Enum.filter(translation["functions"], &(&1["def_id"] == function["def_id"])),
         [%{"lean_name" => type}] <- Enum.filter(translation["types"], &(&1["def_id"] == type_id)) do
      %{"lean" => type, "encoder" => encoder, "encoder_definition_id" => function["def_id"]}
    else
      _ ->
        raise ArgumentError,
              "missing, opaque or mismatched first-party Rustler Encoder for result type #{type_id}"
    end
  end

  def external_names(models) do
    if Enum.any?(Map.values(models), &Map.has_key?(&1, :encoder_trait)) do
      %{
        "trait_decls" => [
          %{
            "rust_pattern" => "rustler::types::Encoder",
            "extract_name" => "Lynx.Rustler.Encoder",
            "constructor" => "Lynx.Rustler.Encoder.mk"
          }
        ],
        "trait_items" => [
          %{
            "trait" => "rustler::types::Encoder",
            "kind" => "method",
            "rust" => "encode",
            "extract" => "encode"
          }
        ]
      }
    else
      %{}
    end
  end

  defp shape(scope, self, ctx) do
    cond do
      scope == path(~w(atom)) and named?(self, ~w(rustler types atom Atom), [], ctx) ->
        {"atom", "rustler::types::atom::Atom", 0, 0}

      scope == path(~w(primitive)) and
          self == %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}} ->
        {"u64", "u64", 0, 0}

      scope == path(~w(string)) and named?(self, ~w(alloc string String), [], ctx) ->
        {"string", "alloc::string::String", 0, 0}

      scope == path(~w(string)) and
        match?(%{"Ref" => [_, %{"Adt" => %{"builtin" => "Str"}}, "Shared"]}, self) and
          self["Ref"] |> hd() == region(0) ->
        {"str", "&'0 str", 0, 1}

      scope == [] and self == reference(region(0), variable(0)) ->
        {"shared", "&'0 @T", 1, 1}

      scope == path(~w(tuple)) and match?(%{"Adt" => %{"builtin" => "Tuple"}}, self) and
          self["Adt"]["generics"] == arguments([variable(0), variable(1)]) ->
        {"pair", "(@A, @B)", 2, 0}

      scope == path(~w(list)) and named?(self, ~w(alloc vec Vec), [variable(0)], ctx) ->
        {"vec", "alloc::vec::Vec<@T>", 1, 0}

      true ->
        nil
    end
  end

  defp signature?(function, self, inherited, ctx) do
    sig = expand(function["signature"], ctx)

    sig["is_unsafe"] == false and sig["is_variadic"] == false and sig["abi"] == "Rust" and
      sig["inputs"] == [
        reference(region(inherited + 1), self),
        named(ctx, ~w(rustler env Env), [region(inherited)], [])
      ] and
      sig["output"] == named(ctx, ~w(rustler term Term), [region(inherited)], [])
  end

  defp parameters?(params, regions, types, trait, ctx) do
    Enum.map(params["regions"], & &1["index"]) == indices(regions) and
      Enum.map(params["types"], & &1["index"]) == indices(types) and
      params["const_generics"] == [] and params["trait_type_constraints"] == [] and
      Enum.map(params["trait_clauses"], fn clause ->
        {clause["clause_id"], expand(clause["trait_"], ctx)}
      end) ==
        Enum.map(indices(types), fn index ->
          {index,
           %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => trait, "generics" => arguments([variable(index)])}
           }}
        end)
  end

  defp trait?(id, ctx) do
    with %{
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
               "skip_binder" => %{"name" => "encode", "signature" => sig, "default" => nil}
             }
           ]
         } <-
           declaration(ctx, "trait_decls", id) do
      name == path(~w(rustler types Encoder)) and
        params["regions"] == [] and length(params["types"]) == 1 and
        params["types"] |> hd() |> Map.get("index") == 0 and
        params["const_generics"] == [] and params["trait_clauses"] == [] and
        params["outlives"] == [] and params["trait_type_constraints"] == [] and
        method_params["types"] == [] and
        Enum.map(method_params["regions"], & &1["index"]) == [0, 1] and
        method_params["const_generics"] == [] and method_params["trait_clauses"] == [] and
        method_params["outlives"] == [] and method_params["trait_type_constraints"] == [] and
        signature?(%{"signature" => free_bound(expand(sig, ctx))}, variable(0), 0, ctx)
    else
      _ -> false
    end
  end

  defp outlives?(kind, function, impl, count, ctx) do
    {expected_function, expected_impl} =
      case kind do
        "shared" ->
          {[outlives(region(0), region(2)), outlives(%{"Lub" => variable(0)}, region(0))],
           [outlives(%{"Lub" => variable(0)}, region(0))]}

        "str" ->
          {[outlives(region(0), region(2))], []}

        kind when kind in ["pair", "vec"] ->
          {Enum.map(indices(count), &outlives(%{"Lub" => variable(&1)}, region(1))), []}

        _ ->
          {[], []}
      end

    expand(function["outlives"], ctx) == expected_function and
      expand(impl["outlives"], ctx) == expected_impl
  end

  def audit(functions, models, translated, refs) do
    if Enum.any?(Map.values(models), &Map.has_key?(&1, :encoder_trait)),
      do: audit_selected(functions, models, translated, refs),
      else: {:ok, %{}}
  end

  defp audit_selected(functions, models, translated, refs) do
    ctx =
      context(translated, refs)
      |> Map.merge(%{
        models: models,
        functions: Map.new(Enum.reject(translated["fun_decls"], &is_nil/1), &{&1["def_id"], &1}),
        implementations: MapSet.new(functions, & &1["def_id"])
      })

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
        %{encoder_trait: trait, encoder_slots: count, encoder_regions: regions} ->
          unless length(args["types"]) == count and length(args["trait_refs"]) == count and
                   length(args["regions"]) == regions and args["const_generics"] == [],
                 do: fail!()

          Enum.zip(args["trait_refs"], args["types"])
          |> Enum.flat_map(fn {ref, self} ->
            reference!(ref, trait, expand(self, ctx), ctx, [])
          end)

        _ ->
          []
      end

    direct ++ Enum.flat_map(Map.values(node), &dispatches(&1, ctx))
  end

  defp dispatches(map, ctx) when is_map(map),
    do: Enum.flat_map(Map.values(map), &dispatches(&1, ctx))

  defp dispatches(list, ctx) when is_list(list), do: Enum.flat_map(list, &dispatches(&1, ctx))
  defp dispatches(_, _), do: []

  defp reference!(ref, trait, self, ctx, seen) do
    with %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => actual}},
           "trait_decl_ref" => %{"id" => ^trait, "generics" => trait_args}
         } <- trait_reference(ref, ctx),
         true <- expand(trait_args, ctx) == arguments([self]),
         true <- {impl_id, self} not in seen,
         %{
           "src" => "Normal",
           "is_negative" => false,
           "is_unsafe" => false,
           "consts" => [],
           "types" => [],
           "implied_trait_refs" => [],
           "impl_trait" => impl_trait,
           "generics" => params,
           "methods" => [%{"skip_binder" => %{"id" => method}}]
         } = impl <- declaration(ctx, "trait_impls", impl_id),
         true <- instance_arguments?(actual, params),
         true <-
           instantiate(expand(impl_trait, ctx), actual, ctx) == %{
             "id" => trait,
             "generics" => arguments([self])
           },
         %{} = function <- ctx.functions[method],
         true <- FormatModels.method_identity?(function, impl, trait, ctx) do
      case ctx.models[method] do
        %{encoder_standard: true, encoder_trait: ^trait, encoder_slots: count} ->
          unless length(actual["types"]) == count and length(actual["trait_refs"]) == count,
            do: fail!()

          [
            method
            | Enum.zip(actual["trait_refs"], actual["types"])
              |> Enum.flat_map(fn {nested, inner} ->
                reference!(nested, trait, expand(inner, ctx), ctx, [{impl_id, self} | seen])
              end)
          ]

        _ ->
          if MapSet.member?(ctx.implementations, method) and Constants.empty_arguments?(actual) and
               params["regions"] == [] and params["types"] == [] and
               params["const_generics"] == [] and
               params["trait_clauses"] == [] and params["outlives"] == [] and
               params["trait_type_constraints"] == [] and
               signature?(function, self, 0, ctx), do: [method], else: fail!()
      end
    else
      _ -> fail!()
    end
  end

  defp instance_arguments?(
         %{"regions" => rs, "types" => ts, "const_generics" => [], "trait_refs" => refs},
         params
       ),
       do:
         length(rs) == length(params["regions"]) and length(ts) == length(params["types"]) and
           length(refs) == length(params["trait_clauses"])

  defp instance_arguments?(_, _), do: false

  defp instantiate(%{"TypeVar" => %{"Free" => index}}, args, ctx),
    do: expand(Enum.at(args["types"], index), ctx)

  defp instantiate(%{"Var" => %{"Free" => index}}, args, _), do: Enum.at(args["regions"], index)

  defp instantiate(map, args, ctx) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, instantiate(v, args, ctx)} end)

  defp instantiate(list, args, ctx) when is_list(list),
    do: Enum.map(list, &instantiate(&1, args, ctx))

  defp instantiate(value, _, _), do: value

  defp trait_reference(
         %{"regions" => [], "outlives" => [], "skip_binder" => %{"Value" => [_, value]}},
         _
       ),
       do: value

  defp trait_reference(
         %{"regions" => [], "outlives" => [], "skip_binder" => %{"Deduplicated" => id}},
         ctx
       ),
       do: ctx.traits[id]

  defp trait_reference(_, _), do: nil

  defp outlives(left, right),
    do: %{"regions" => [], "outlives" => [], "skip_binder" => [left, right]}

  defp fail!,
    do:
      raise(
        ArgumentError,
        "Encoder requires an extracted monomorphic implementation or an approved typed runtime method with matching dictionary, method identity and signature"
      )

  defp named(ctx, name, regions, types) do
    case Enum.find(ctx.translated["type_decls"], &(&1 && &1["item_meta"]["name"] == path(name))) do
      %{"def_id" => id} ->
        %{
          "Adt" => %{
            "id" => id,
            "builtin" => nil,
            "generics" => %{arguments(types) | "regions" => regions}
          }
        }

      _ ->
        nil
    end
  end

  defp named?(type, name, types, ctx), do: type == named(ctx, name, [], types)

  defp context(translated, refs),
    do: %{translated: translated, refs: refs, traits: trait_references(translated, %{})}

  defp declaration(ctx, key, id), do: Enum.find(ctx.translated[key], &(&1 && &1["def_id"] == id))
  defp expand(value, ctx), do: CallModels.expand(value, ctx.refs)
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp variable(index), do: %{"TypeVar" => %{"Free" => index}}
  defp region(index), do: %{"Var" => %{"Free" => index}}
  defp reference(region, type), do: %{"Ref" => [region, type, "Shared"]}
  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))
  defp free_bound(%{"Var" => %{"Bound" => [0, index]}}), do: region(index)
  defp free_bound(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free_bound(v)} end)
  defp free_bound(list) when is_list(list), do: Enum.map(list, &free_bound/1)
  defp free_bound(value), do: value

  defp trait_references(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = value]}, refs) do
    if Map.has_key?(refs, id) and refs[id] != value,
      do: raise(ArgumentError, "inconsistent LLBC shared trait identity")

    trait_references(value, Map.put(refs, id, value))
  end

  defp trait_references(map, refs) when is_map(map),
    do: Enum.reduce(Map.values(map), refs, &trait_references/2)

  defp trait_references(list, refs) when is_list(list),
    do: Enum.reduce(list, refs, &trait_references/2)

  defp trait_references(_, refs), do: refs
end
