defmodule Lynx.Rust.NativeDropLowering do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, NativeDrops}

  # A consuming `drop(place)` and `core::mem::drop(move place)` have the same
  # ownership action. Use the actual compiler declaration and checked destructor
  # dictionary, preserving every other statement and all source locations.
  def lower!(document, first_party, opts \\ []) do
    {document, unwind_drop} =
      if opts[:unwind] == :captured,
        do: Lynx.Rust.NativeUnwindDrops.prepare!(document),
        else: {document, nil}

    if NativeDrops.needs_lowering?(document),
      do: do_lower!(document, first_party, unwind_drop),
      else: {document, []}
  end

  defp do_lower!(document, first_party, unwind_drop) do
    translated = document["translated"]
    refs = LLBC.type_references!(document)

    mem_drop =
      Enum.find(translated["fun_decls"], fn f ->
        f &&
          match?(
            %{native_dispose: true},
            NativeDrops.resolve(f, translated, refs) ||
              Lynx.Rust.FileDrops.resolve(f, translated, refs)
          )
      end)

    functions = translated["fun_decls"]

    initial = %{next_ref: max_value(document) + 1, sites: []}

    {functions, state} =
      Enum.map_reduce(functions, initial, fn function, state ->
        if function && first_party?(function, first_party) && is_map(function["body"]) do
          locals = function["body"]["Structured"]["locals"]["locals"]

          context = %{
            translated: translated,
            refs: refs,
            mem_drop: mem_drop,
            unwind_drop: unwind_drop,
            function: function,
            locals: Map.new(locals, &{&1["index"], &1["ty"]}),
            local_template: hd(locals)
          }

          {body, state} =
            walk(
              function["body"]["Structured"]["body"],
              context,
              Map.merge(state, %{next_local: length(locals), new_locals: []}),
              false
            )

          function =
            function
            |> put_in(["body", "Structured", "body"], body)
            |> put_in(
              ["body", "Structured", "locals", "locals"],
              locals ++ Enum.reverse(state.new_locals)
            )

          {function, Map.drop(state, [:next_local, :new_locals])}
        else
          {function, state}
        end
      end)

    {put_in(document, ["translated", "fun_decls"], functions), Enum.reverse(state.sites)}
  end

  defp walk(%{"kind" => %{"Drop" => drop}} = statement, ctx, state, cleanup) do
    case NativeDrops.site(drop, ctx.translated, ctx.refs) do
      {:ok, _site} when cleanup and is_nil(ctx.unwind_drop) ->
        walk_children(statement, ctx, state, cleanup)

      {:ok, site} ->
        if cleanup and site.native_kind not in [:guard, :mutex],
          do:
            LLBC.failure!(
              ctx.function,
              ctx.translated,
              "unsupported native destructor during captured unwind"
            )

        if cleanup and site.native_kind == :mutex and
             not NativeDrops.destructor_free?(site.payload, ctx.translated, ctx.refs),
           do:
             LLBC.failure!(
               ctx.function,
               ctx.translated,
               "captured unwind requires a destructor-free mutex payload"
             )

        mem_drop = if cleanup, do: ctx.unwind_drop, else: ctx.mem_drop

        unless ctx.mem_drop,
          do:
            raise(
              ArgumentError,
              "native drop lowering requires the actual core::mem::drop declaration"
            )

        unless same_runtime_type?(
                 place_type!(drop["place"], ctx),
                 CallModels.expand(site.self, ctx.refs)
               ),
               do:
                 LLBC.failure!(
                   ctx.function,
                   ctx.translated,
                   "native dropped place has an inconsistent owned type"
                 )

        # Introduce one fresh type-table entry before its use in the body;
        # the library declaration can occur later in the serialized crate.
        unit = %{
          "Value" => [
            state.next_ref + 1,
            CallModels.expand(ctx.mem_drop["signature"]["output"], ctx.refs)
          ]
        }

        unit_ref = %{"Deduplicated" => state.next_ref + 1}
        dest = %{"kind" => %{"Local" => state.next_local}, "ty" => unit_ref}

        dictionary = %{
          "regions" => [],
          "outlives" => [],
          "skip_binder" => %{
            "Value" => [
              state.next_ref,
              %{
                "kind" => %{
                  "TraitImpl" => %{
                    "id" => site.impl,
                    "generics" => Map.get(site, :impl_arguments, arguments([site.payload]))
                  }
                },
                "trait_decl_ref" => %{"id" => site.trait, "generics" => arguments([site.self])}
              }
            ]
          }
        }

        call = %{
          "func" => %{
            "Regular" => %{
              "kind" => %{"Fun" => mem_drop["def_id"]},
              "generics" => Map.put(arguments([site.self]), "trait_refs", [dictionary])
            }
          },
          "args" => [%{"Move" => drop["place"]}],
          "safety" => "Inherit"
        }

        kind = %{"Call" => %{"call" => call, "dest" => dest, "on_unwind" => drop["on_unwind"]}}

        record = %{
          caller: ctx.function["def_id"],
          statement: statement["id"],
          destructor: site.function,
          type: CallModels.expand(site.self, ctx.refs),
          consuming_call: mem_drop["def_id"],
          unwind: cleanup
        }

        state = %{
          state
          | next_ref: state.next_ref + 2,
            next_local: state.next_local + 1,
            new_locals: [
              Map.merge(ctx.local_template, %{
                "index" => state.next_local,
                "name" => nil,
                "span" => reference(ctx.local_template["span"]),
                "drop_flag_for" => nil,
                "ty" => unit
              })
              | state.new_locals
            ],
            sites: [record | state.sites]
        }

        # Validate nested cleanup too; never let the backend's ignored unwind
        # blocks hide another effectful destructor.
        {kind, state} = walk_children(kind, ctx, state, cleanup)
        {Map.put(statement, "kind", kind), state}

      {:error, _message} ->
        walk_children(statement, ctx, state, cleanup)

      nil ->
        walk_children(statement, ctx, state, cleanup)
    end
  end

  defp walk(value, ctx, state, cleanup), do: walk_children(value, ctx, state, cleanup)

  # Only a local and its owned fields may be consumed. Dereferencing a borrowed
  # aggregate would require reconstructing that borrow after failure or drop.
  def place_type!(place, ctx, borrowed \\ false)

  def place_type!(%{"kind" => kind, "ty" => annotation}, ctx, borrowed) do
    type =
      case kind do
        %{"Projection" => [parent, "PtrMetadata"]} when borrowed ->
          case place_type!(parent, ctx, borrowed) do
            %{"Ref" => [_, %{"Adt" => %{"builtin" => "Str"}}, _]} ->
              %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}

            %{"Ref" => [_, %{"Slice" => _}, _]} ->
              %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}

            _ ->
              LLBC.failure!(
                ctx.function,
                ctx.translated,
                "unsupported native ownership pointer metadata"
              )
          end

        %{"Projection" => [parent, "Deref"]} when borrowed ->
          case place_type!(parent, ctx, borrowed) do
            %{"Ref" => [_, type, _]} ->
              type

            _ ->
              LLBC.failure!(
                ctx.function,
                ctx.translated,
                "unsupported native ownership pointer dereference"
              )
          end

        %{"Local" => local} ->
          CallModels.expand(Map.fetch!(ctx.locals, local), ctx.refs)

        %{"Projection" => [parent, %{"Field" => [variant, index]}]}
        when is_integer(index) and index >= 0 ->
          case place_type!(parent, ctx, borrowed) do
            %{"Adt" => %{"builtin" => "Tuple", "generics" => %{"types" => types}}}
            when is_nil(variant) ->
              Enum.fetch!(types, index)

            %{"Adt" => %{"builtin" => nil, "id" => id, "generics" => args}} ->
              declaration = Enum.find(ctx.translated["type_decls"], &(&1 && &1["def_id"] == id))

              fields =
                case declaration["kind"] do
                  %{"Struct" => fields} when is_nil(variant) ->
                    fields

                  %{"Enum" => variants} ->
                    Enum.find_value(variants, fn row ->
                      if row["id"] == variant, do: row["fields"]
                    end)

                  _ ->
                    nil
                end

              unless is_list(fields) and args["const_generics"] == [] and
                       length(args["types"]) == length(declaration["generics"]["types"]) and
                       length(args["regions"]) == length(declaration["generics"]["regions"]),
                     do:
                       LLBC.failure!(
                         ctx.function,
                         ctx.translated,
                         "unsupported owned drop field instantiation"
                       )

              field = Enum.fetch!(fields, index)
              CallModels.instantiate(CallModels.expand(field["ty"], ctx.refs), args)

            _ ->
              LLBC.failure!(
                ctx.function,
                ctx.translated,
                "native drop projection requires an owned aggregate"
              )
          end

        _ ->
          LLBC.failure!(
            ctx.function,
            ctx.translated,
            "native drop cannot consume through a borrowed or raw pointer"
          )
      end

    # rustc instantiates and freshens lifetimes at accesses. They do not change
    # runtime ownership; retain region arity, generic identity and borrow kind.
    # The original region identities remain in LLBC for Aeneas's borrow checks.
    unless same_runtime_type?(type, CallModels.expand(annotation, ctx.refs)),
      do:
        LLBC.failure!(
          ctx.function,
          ctx.translated,
          "native dropped place has an inconsistent field type"
        )

    type
  end

  def place_type!(_, ctx, _),
    do:
      LLBC.failure!(
        ctx.function,
        ctx.translated,
        "native owner lifetime: invalid place annotation"
      )

  def same_runtime_type?(left, right), do: erase_regions(left) == erase_regions(right)

  defp erase_regions(%{"Ref" => [_, type, kind]}),
    do: %{"Ref" => ["Erased", erase_regions(type), kind]}

  defp erase_regions(map) when is_map(map),
    do:
      Map.new(map, fn
        {"regions", regions} when is_list(regions) ->
          {"regions", Enum.map(regions, fn _ -> "Erased" end)}

        {key, value} ->
          {key, erase_regions(value)}
      end)

  defp erase_regions(list) when is_list(list), do: Enum.map(list, &erase_regions/1)
  defp erase_regions(value), do: value

  defp walk_children(map, ctx, state, cleanup) when is_map(map) do
    {pairs, state} =
      Enum.map_reduce(Enum.sort(map), state, fn {key, value}, state ->
        {value, state} = walk(value, ctx, state, cleanup or key in ["on_unwind", "on_failure"])
        {{key, value}, state}
      end)

    {Map.new(pairs), state}
  end

  defp walk_children(list, ctx, state, cleanup) when is_list(list),
    do: Enum.map_reduce(list, state, &walk(&1, ctx, &2, cleanup))

  defp walk_children(value, _, state, _), do: {value, state}

  defp first_party?(%{"item_meta" => %{"name" => [%{"Ident" => [crate, _]} | _]}}, crates),
    do: crate in crates

  defp first_party?(_, _), do: false

  defp reference(%{"Value" => [id, _]}), do: %{"Deduplicated" => id}
  defp reference(value), do: value
  defp max_value(%{"Value" => [id, value]}), do: max(id, max_value(value))
  defp max_value(map) when is_map(map), do: max_value(Map.values(map))
  defp max_value(list) when is_list(list), do: Enum.reduce(list, 0, &max(max_value(&1), &2))
  defp max_value(_), do: 0

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}
end
