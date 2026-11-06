defmodule Lynx.Rust.DropModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants}

  @string_model "Logical heap String deallocation model: no observable value, mutation or panic; allocator effects, exhaustion and native deallocation correctness are unverified"

  def generated?(%{"item_meta" => %{"name" => name}}) when is_list(name),
    do: match?(%{"Builtin" => ["DropGlue", 0]}, List.last(name))

  def generated?(_), do: false

  # Aeneas removes Destruct items and evaluates Drop as ownership removal. Admit
  # that erasure only after checking each actual compiler-generated body. This
  # does not implement general Drop or assume a first-party destructor contract.
  def audit(functions, generated, translated, refs, first_party) do
    ctx = %{
      translated: translated,
      refs: refs,
      first_party: first_party,
      functions: declarations(translated["fun_decls"]),
      types: declarations(translated["type_decls"]),
      traits: declarations(translated["trait_decls"]),
      impls: declarations(translated["trait_impls"]),
      constants: constant_references(translated, %{})
    }

    Enum.reduce_while(functions ++ generated, {:ok, %{erasures: %{}, sites: %{}}}, fn function,
                                                                                      {:ok,
                                                                                       result} ->
      try do
        {entries, ids} =
          if generated?(function) do
            {_, entries} = destructor!(function["def_id"], nil, ctx, [])
            {entries, []}
          else
            locals =
              case function["body"] do
                %{"Structured" => %{"locals" => %{"locals" => locals}}} -> locals
                _ -> []
              end

            local_ctx =
              Map.put(ctx, :locals, Map.new(locals, &{&1["index"], expand(&1["ty"], ctx)}))

            Enum.reduce(drops(function["body"]), {%{}, []}, fn drop, {entries, ids} ->
              place!(drop["place"], local_ctx)
              {id, found} = site!(drop, local_ctx, [])
              {Map.merge(entries, found), [id | ids]}
            end)
          end

        {:cont,
         {:ok,
          %{
            erasures: Map.merge(result.erasures, entries),
            sites: Map.put(result.sites, function["def_id"], Enum.uniq(ids) |> Enum.sort())
          }}}
      rescue
        error in ArgumentError -> {:halt, {:error, function, Exception.message(error)}}
      end
    end)
  end

  def link!(audit, translation) do
    for {id, _model} <- audit.erasures,
        Enum.any?(translation["functions"], &(&1["def_id"] == id)),
        do: reject!("Aeneas did not erase the audited Destruct item #{id}")

    :ok
  end

  def report(audit) do
    audit.erasures
    |> Map.values()
    |> Enum.map(&Map.drop(&1, [:self]))
    |> Enum.sort_by(& &1.rust_name)
  end

  # Charon preserves both the element and allocator parameters on Vec's
  # generated drop even though it removes the allocator from the Vec type.
  # Erasure is restricted to bytes and Global: neither has an element/custom
  # allocator destructor. Native deallocation remains an explicit heap model.
  defp site!(
         %{
           "kind" => "Precise",
           "place" => %{"ty" => annotation},
           "fn_ptr" => %{
             "kind" => %{"Fun" => id},
             "generics" => %{
               "regions" => [%{"Body" => region}],
               "types" => [element, allocator],
               "const_generics" => [],
               "trait_refs" => []
             }
           }
         },
         ctx,
         _seen
       )
       when is_integer(region) do
    u8 = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}
    t = %{"TypeVar" => %{"Free" => 0}}
    a = %{"TypeVar" => %{"Free" => 1}}
    vector_name = path(~w(alloc vec Vec))

    with ^u8 <- expand(element, ctx),
         %{"Adt" => %{"id" => allocator_id, "builtin" => nil, "generics" => allocator_args}} <-
           expand(allocator, ctx),
         true <- Constants.empty_arguments?(allocator_args),
         %{"item_meta" => %{"name" => allocator_name}, "generics" => allocator_params} <-
           ctx.types[allocator_id],
         true <-
           allocator_name == path(~w(alloc alloc Global)) and parameters?(allocator_params, 0, 0),
         %{"Adt" => %{"id" => vector_id, "builtin" => nil, "generics" => actual_args}} = self <-
           expand(annotation, ctx),
         true <- actual_args == arguments([u8]),
         %{
           "item_meta" => %{"name" => ^vector_name},
           "generics" => vector_params,
           "kind" => "Opaque"
         } <- ctx.types[vector_id],
         true <- parameters?(vector_params, 0, 1),
         generic_self = %{
           "Adt" => %{"id" => vector_id, "builtin" => nil, "generics" => arguments([t])}
         },
         function when not is_nil(function) <- ctx.functions[id],
         %{
           "body" => "Opaque",
           "generics" => params,
           "signature" => %{
             "is_unsafe" => true,
             "abi" => "Rust",
             "is_variadic" => false,
             "inputs" => [input],
             "output" => output
           },
           "src" => %{
             "TraitImpl" => %{
               "impl_ref" => %{"id" => impl_id, "generics" => impl_args},
               "trait_ref" => %{"id" => trait_id, "generics" => trait_args},
               "item_id" => 0,
               "reuses_default" => false
             }
           }
         } <- function,
         # Check the generic shape and Vec's specific lifetime bounds separately.
         true <- parameters?(Map.put(params, "outlives", []), 1, 2),
         true <- vector_outlives?(expand(params, ctx)["outlives"], t, a),
         true <-
           expand(input, ctx) == %{"Ref" => [%{"Var" => %{"Free" => 0}}, generic_self, "Mut"]},
         true <- unit?(expand(output, ctx)),
         true <-
           function["item_meta"]["name"] ==
             vector_name ++ [%{"Impl" => %{"Trait" => impl_id}}, %{"Builtin" => ["DropGlue", 0]}],
         true <- expand(impl_args, ctx) == arguments([t, a]),
         true <- destruct_trait?(trait_id, ctx),
         expected_trait = %{"id" => trait_id, "generics" => arguments([generic_self])},
         true <- expand(trait_args, ctx) == arguments([generic_self]),
         %{
           "src" => "Destruct",
           "item_meta" => %{"name" => impl_name},
           "generics" => impl_params,
           "is_negative" => false,
           "is_unsafe" => false,
           "types" => [],
           "consts" => [],
           "implied_trait_refs" => [],
           "impl_trait" => impl_trait,
           "methods" => [method]
         } <- ctx.impls[impl_id],
         true <- impl_name == vector_name ++ [%{"Impl" => %{"Trait" => impl_id}}],
         true <- parameters?(impl_params, 0, 2) and impl_params["outlives"] == [],
         true <- expand(impl_trait, ctx) == expected_trait,
         %{
           "params" => method_params,
           "kind" => %{"TraitMethod" => [^trait_id, 0]},
           "skip_binder" => %{"id" => ^id, "generics" => method_args}
         } <- method,
         true <- parameters?(method_params, 1, 0) and method_params["outlives"] == [],
         true <-
           expand(method_args, ctx) ==
             Map.put(arguments([t, a]), "regions", [%{"Var" => %{"Bound" => [0, 0]}}]) do
      {id,
       %{
         id => %{
           definition_id: id,
           rust_name: render_name(function["item_meta"]["name"]),
           type: "alloc::vec::Vec<u8>",
           self: self,
           first_party: false,
           status: :modelled,
           implementation_verified: false,
           dependencies: [],
           label:
             "Logical heap Vec<u8>/Global deallocation model: no element destructor; native allocator effects and deallocation correctness unverified"
         }
       }}
    else
      _ ->
        reject!(
          "unsupported or inconsistent Vec drop element, allocator, signature or dictionary"
        )
    end
  end

  defp site!(drop, ctx, seen) do
    with %{
           "place" => %{"ty" => type},
           "fn_ptr" => %{"kind" => %{"Fun" => id}, "generics" => args},
           "kind" => "Precise"
         } <- drop,
         true <- arguments?(args, 1) do
      {_, entries} = destructor!(id, expand(type, ctx), ctx, seen)
      {id, entries}
    else
      _ -> reject!("unsupported or inconsistent Rust drop site")
    end
  end

  defp vector_outlives?(outlives, t, a),
    do:
      outlives ==
        Enum.map([t, a], fn type ->
          %{
            "outlives" => [],
            "regions" => [],
            "skip_binder" => [%{"Lub" => type}, %{"Var" => %{"Free" => 0}}]
          }
        end)

  defp destructor!(id, expected, ctx, seen) do
    if id in seen, do: reject!("recursive destructor dependency")
    function = ctx.functions[id]

    with %{
           "signature" => %{
             "is_unsafe" => true,
             "abi" => "Rust",
             "is_variadic" => false,
             "inputs" => [input],
             "output" => output
           },
           "generics" => params,
           "src" => %{
             "TraitImpl" => %{
               "impl_ref" => %{"id" => impl_id, "generics" => impl_args},
               "trait_ref" => trait_ref,
               "item_id" => 0,
               "reuses_default" => false
             }
           },
           "item_meta" => %{"name" => name}
         } <- function,
         true <- parameters?(params, 1, 0),
         %{"Ref" => [%{"Var" => %{"Free" => 0}}, self, "Mut"]} <- expand(input, ctx),
         true <- expected == nil or expected == self,
         true <- unit?(expand(output, ctx)),
         %{"Adt" => %{"id" => type_id, "builtin" => nil, "generics" => type_args}} <- self,
         true <- Constants.empty_arguments?(type_args),
         %{"item_meta" => %{"name" => type_name}, "generics" => type_params} <- ctx.types[type_id],
         true <- parameters?(type_params, 0, 0),
         true <-
           name ==
             type_name ++ [%{"Impl" => %{"Trait" => impl_id}}, %{"Builtin" => ["DropGlue", 0]}],
         true <- Constants.empty_arguments?(impl_args),
         true <- destruct_trait?(trait_ref["id"], ctx),
         true <- expand(trait_ref["generics"], ctx) == arguments([self]),
         %{
           "src" => "Destruct",
           "is_negative" => false,
           "is_unsafe" => false,
           "generics" => impl_params,
           "impl_trait" => impl_trait,
           "consts" => [],
           "types" => [],
           "implied_trait_refs" => [],
           "methods" => [method]
         } <- ctx.impls[impl_id],
         true <- parameters?(impl_params, 0, 0),
         true <-
           expand(impl_trait, ctx) == %{"id" => trait_ref["id"], "generics" => arguments([self])},
         true <- method?(method, id, trait_ref["id"]) do
      type!(self, ctx, [])
      first_party = first_party?(type_name, ctx)

      dependencies =
        cond do
          first_party ->
            with %{
                   "Structured" => %{
                     "locals" => %{"arg_count" => 1, "locals" => locals},
                     "body" => body
                   }
                 } <- function["body"],
                 true <- function["item_meta"]["opacity"] == "Transparent",
                 true <- Enum.map(locals, & &1["index"]) == Enum.to_list(0..(length(locals) - 1)) do
              local_types = Map.new(locals, &{&1["index"], expand(&1["ty"], ctx)})

              unless unit?(local_types[0]) and
                       match?(%{"Ref" => [_, ^self, "Mut"]}, local_types[1]),
                     do: reject!("inconsistent drop glue locals")

              block!(body, Map.put(ctx, :locals, local_types), [id | seen])
            else
              _ -> reject!("missing compiler-generated structural drop body")
            end

          type_name == path(~w(alloc string String)) and function["body"] == "Opaque" ->
            %{}

          true ->
            reject!("unapproved external destructor #{inspect(type_name)}")
        end

      entry = %{
        definition_id: id,
        rust_name: render_name(name),
        type: render_name(type_name),
        self: self,
        first_party: first_party,
        status: if(first_party, do: :audited_erasure, else: :modelled),
        implementation_verified: false,
        dependencies: Map.keys(dependencies) |> Enum.sort(),
        label:
          if(first_party,
            do:
              "Compiler-generated structural drop checked for erasure under the logical heap deallocation model; no Lean implementation theorem claimed",
            else: @string_model
          )
      }

      {self, Map.put(dependencies, id, entry)}
    else
      _ ->
        reject!(
          "missing or inconsistent compiler-generated destructor identity, type or signature (function #{inspect(id)})"
        )
    end
  end

  # Every admitted statement is administrative, observes a valid enum tag, or
  # recursively drops a supported field. Calls, assertions, arithmetic, mutation
  # through self, loops and panics are excluded even inside unused branches.
  defp block!(%{"statements" => statements}, ctx, seen) when is_list(statements) do
    Enum.reduce(statements, %{}, fn %{"kind" => kind}, entries ->
      found =
        case kind do
          %{"StorageLive" => local} ->
            local!(local, ctx)
            %{}

          %{"StorageDead" => local} ->
            local!(local, ctx)
            %{}

          "Return" ->
            %{}

          terminal when terminal in ["UnwindResume", "UnwindTerminate"] ->
            unless ctx[:cleanup], do: reject!("observable unwind in drop glue")
            %{}

          %{
            "Assign" => [
              %{"kind" => %{"Local" => 0}, "ty" => type},
              %{"Aggregate" => [%{"Adt" => [adt, nil, nil]}, []]}
            ]
          } ->
            unless unit?(expand(type, ctx)) and unit?(%{"Adt" => expand(adt, ctx)}),
              do: reject!("non-unit drop glue assignment")

            %{}

          %{"Drop" => drop} ->
            place_type = place!(drop["place"], ctx)

            unless place_type == expand(drop["place"]["ty"], ctx),
              do: reject!("inconsistent dropped field type")

            {_, found} = site!(drop, ctx, seen)
            Map.merge(found, block!(drop["on_unwind"], Map.put(ctx, :cleanup, true), seen))

          %{"Switch" => %{"data" => data, "branches" => branches}} when is_list(branches) ->
            with %{"Discriminant" => place} <- data["scrutinee"],
                 %{"Adt" => adt} <- place!(place, ctx),
                 %{"kind" => %{"Enum" => variants}} <- ctx.types[adt["id"]],
                 true <- switch?(data, adt, variants, length(branches), ctx) do
              Enum.reduce(branches, %{}, &Map.merge(&2, block!(&1, ctx, seen)))
            else
              _ -> reject!("unsupported structural drop switch")
            end

          _ ->
            reject!(
              "observable or unsupported behavior in compiler-generated drop glue: #{inspect(kind, limit: 8)}"
            )
        end

      Map.merge(entries, found)
    end)
  end

  defp block!(_, _, _), do: reject!("missing structural drop block")

  defp place!(%{"kind" => kind, "ty" => annotation}, ctx) do
    type =
      case kind do
        %{"Local" => local} ->
          local!(local, ctx)

        %{"Projection" => [parent, "Deref"]} ->
          case place!(parent, ctx) do
            %{"Ref" => [_, type, kind]} when kind in ["Shared", "Mut"] -> type
            _ -> reject!("unsupported drop pointer dereference")
          end

        %{"Projection" => [parent, %{"Field" => [variant, index]}]}
        when is_integer(index) and index >= 0 ->
          case place!(parent, ctx) do
            %{"Adt" => %{"id" => id, "builtin" => nil}} ->
              field!(ctx.types[id], variant, index, ctx)

            _ ->
              reject!("unsupported dropped field projection")
          end

        _ ->
          reject!("unsupported structural drop place")
      end

    unless type == expand(annotation, ctx), do: reject!("inconsistent structural drop place type")
    type
  end

  defp place!(_, _), do: reject!("missing structural drop place")

  defp field!(%{"kind" => %{"Enum" => variants}}, variant, index, ctx) do
    fields = Enum.find_value(variants, fn v -> if v["id"] == variant, do: v["fields"] end)
    field_type!(fields, index, ctx)
  end

  defp field!(%{"kind" => %{"Struct" => fields}}, nil, index, ctx),
    do: field_type!(fields, index, ctx)

  defp field!(_, _, _, _), do: reject!("unsupported structural drop field")

  defp field_type!(fields, index, ctx) when is_list(fields) do
    case Enum.at(fields, index) do
      %{"ty" => type} -> expand(type, ctx)
      _ -> reject!("missing structural drop field")
    end
  end

  defp field_type!(_, _, _), do: reject!("missing structural drop variant")

  defp type!(%{"Scalar" => "Bool"}, _, _), do: :ok

  defp type!(%{"Scalar" => %{"Integer" => %{"Signed" => width}}}, _, _)
       when width in ~w(I8 I16 I32 I64 I128 Isize), do: :ok

  defp type!(%{"Scalar" => %{"Integer" => %{"Unsigned" => width}}}, _, _)
       when width in ~w(U8 U16 U32 U64 U128 Usize), do: :ok

  defp type!(%{"Ref" => [_, _, "Shared"]}, _, _), do: :ok

  defp type!(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}, ctx, seen) do
    unless args["regions"] == [] and args["const_generics"] == [] and args["trait_refs"] == [],
      do: reject!("generic drop tuple")

    Enum.each(args["types"], &type!(&1, ctx, seen))
  end

  defp type!(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}}, ctx, seen) do
    if id in seen or not Constants.empty_arguments?(args),
      do: reject!("recursive or generic owned drop type")

    with %{"item_meta" => %{"name" => name}, "generics" => params, "kind" => kind} <-
           ctx.types[id],
         true <- parameters?(params, 0, 0) do
      case {name, kind} do
        {name, "Opaque"}
        when name == [
               %{"Ident" => ["alloc", 0]},
               %{"Ident" => ["string", 0]},
               %{"Ident" => ["String", 0]}
             ] ->
          :ok

        {name, %{"Struct" => fields}} ->
          unless first_party?(name, ctx), do: reject!("unapproved external owned drop type")
          Enum.each(fields, &type!(expand(&1["ty"], ctx), ctx, [id | seen]))

        {name, %{"Enum" => variants}} ->
          unless first_party?(name, ctx), do: reject!("unapproved external owned drop type")

          Enum.each(variants, fn v ->
            Enum.each(v["fields"], &type!(expand(&1["ty"], ctx), ctx, [id | seen]))
          end)

        _ ->
          reject!("unsupported owned drop type")
      end
    else
      _ -> reject!("missing owned drop type")
    end
  end

  defp type!(_, _, _), do: reject!("unsupported owned drop type")

  defp switch?(data, adt, variants, count, ctx) do
    valid_branch = fn branch -> is_integer(branch) and branch >= 0 and branch < count end

    is_list(data["branches"]) and (data["fallback"] == nil or valid_branch.(data["fallback"])) and
      Enum.all?(data["branches"], fn
        [constant, branch] ->
          case constant_value(constant, ctx.constants) do
            [%{"Discriminant" => [^adt, variant]}, type] ->
              Enum.any?(variants, &(&1["id"] == variant)) and valid_branch.(branch) and
                expand(type, ctx) == %{"Scalar" => %{"Integer" => %{"Signed" => "Isize"}}}

            _ ->
              false
          end

        _ ->
          false
      end)
  end

  defp destruct_trait?(id, ctx) do
    case ctx.traits[id] do
      %{
        "item_meta" => %{"name" => name},
        "generics" => params,
        "is_unsafe" => false,
        "consts" => [],
        "types" => [],
        "implied_clauses" => [],
        "methods" => [
          %{
            "params" => method_params,
            "kind" => %{"TraitMethod" => [^id, 0]},
            "skip_binder" => %{"name" => "drop_glue", "signature" => sig, "default" => nil}
          }
        ]
      } ->
        name == path(~w(core marker Destruct)) and parameters?(params, 0, 1) and
          parameters?(method_params, 1, 0) and
          sig["is_unsafe"] == true and sig["abi"] == "Rust" and sig["is_variadic"] == false and
          expand(sig["inputs"], ctx) == [
            %{"Ref" => [%{"Var" => %{"Bound" => [0, 0]}}, %{"TypeVar" => %{"Free" => 0}}, "Mut"]}
          ] and unit?(expand(sig["output"], ctx))

      _ ->
        false
    end
  end

  defp method?(
         %{
           "params" => params,
           "kind" => %{"TraitMethod" => [trait, 0]},
           "skip_binder" => %{"id" => id, "generics" => args}
         },
         id,
         trait
       ),
       do:
         parameters?(params, 1, 0) and
           args == %{
             "regions" => [%{"Var" => %{"Bound" => [0, 0]}}],
             "types" => [],
             "const_generics" => [],
             "trait_refs" => []
           }

  defp method?(_, _, _), do: false

  defp parameters?(
         %{
           "regions" => regions,
           "types" => types,
           "const_generics" => [],
           "trait_clauses" => [],
           "outlives" => [],
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

  defp arguments?(
         %{"regions" => regions, "types" => [], "const_generics" => [], "trait_refs" => []},
         count
       )
       when is_list(regions), do: length(regions) == count

  defp arguments?(_, _), do: false

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp unit?(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}),
    do: Constants.empty_arguments?(args)

  defp unit?(_), do: false
  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))

  defp declarations(items) do
    items = Enum.reject(items || [], &is_nil/1)
    indexed = Map.new(items, &{&1["def_id"], &1})
    if length(items) != map_size(indexed), do: reject!("duplicate declaration identity")
    indexed
  end

  defp expand(type, ctx), do: CallModels.expand(type, ctx.refs)
  defp local!(id, ctx), do: Map.get(ctx.locals, id) || reject!("missing drop glue local")
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp first_party?([%{"Ident" => [crate, _]} | _], ctx), do: crate in ctx.first_party
  defp first_party?(_, _), do: false

  defp render_name(name),
    do:
      Enum.map_join(name, "::", fn
        %{"Ident" => [part, _]} -> part
        %{"Impl" => %{"Trait" => id}} -> "{impl##{id}}"
        %{"Builtin" => [part, _]} -> part
      end)

  defp reject!(reason),
    do: raise(ArgumentError, "Rust structural drop erasure rejected: " <> reason)

  defp drops(%{"Drop" => drop} = node), do: [drop | Enum.flat_map(Map.values(node), &drops/1)]
  defp drops(map) when is_map(map), do: Enum.flat_map(Map.values(map), &drops/1)
  defp drops(list) when is_list(list), do: Enum.flat_map(list, &drops/1)
  defp drops(_), do: []
  defp constant_value(%{"Value" => [_, value]}, _), do: value
  defp constant_value(%{"Deduplicated" => id}, refs), do: refs[id]
  defp constant_value(_, _), do: nil

  defp constant_references(%{"Value" => [id, [%{"Discriminant" => _}, _] = value]}, refs) do
    if Map.has_key?(refs, id) and refs[id] != value,
      do: reject!("inconsistent shared discriminant identity")

    Map.put(refs, id, value)
  end

  defp constant_references(map, refs) when is_map(map),
    do: Enum.reduce(Map.values(map), refs, &constant_references/2)

  defp constant_references(list, refs) when is_list(list),
    do: Enum.reduce(list, refs, &constant_references/2)

  defp constant_references(_, refs), do: refs
end
