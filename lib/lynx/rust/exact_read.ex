defmodule Lynx.Rust.ExactRead do
  @moduledoc false
  alias Lynx.Rust.{CallModels, FileModels, ResourceModels}

  def includes do
    ~w(alloc::io::read::Read::read_exact alloc::io::read::default_read_exact
      core::io::error::_::READ_EXACT_EOF core::io::error::SimpleMessage)
  end

  # These are implementation selections, not external specifications. Each body
  # still passes the ordinary operation, dependency and destruction audits.
  def selected?(%{"body" => %{"Structured" => _}} = function, translated) do
    refs = Lynx.Rust.LLBC.type_references!(translated)

    case function["item_meta"]["name"] do
      [
        %{"Ident" => ["alloc", 0]},
        %{"Ident" => ["io", 0]},
        %{"Ident" => ["read", 0]},
        %{"Ident" => ["default_read_exact", 0]}
      ] ->
        function["src"] == "Normal" and reader?(function, translated, refs)

      [
        %{"Ident" => ["alloc", 0]},
        %{"Ident" => ["io", 0]},
        %{"Ident" => ["read", 0]},
        %{"Ident" => ["Read", 0]},
        %{"Ident" => ["read_exact", 0]}
      ] ->
        reader?(function, translated, refs) and default_method?(function, translated)

      _ ->
        with %{"GlobalInitializer" => %{"id" => id}} <- function["src"],
             [global] <- Enum.filter(translated["global_decls"], &(&1 && &1["def_id"] == id)) do
          constant?(global, refs, translated["type_decls"]) and
            function["def_id"] == Lynx.Rust.Constants.initializer_id(global) and
            function["signature"]["is_unsafe"] == false and
            function["signature"]["is_variadic"] == false and
            function["signature"]["abi"] == "Rust" and
            function["signature"]["inputs"] == [] and
            CallModels.expand(function["signature"]["output"], refs) ==
              CallModels.expand(global["ty"], refs)
        else
          _ -> false
        end
    end
  end

  def selected?(_, _), do: false

  # The upstream trait builder unfolds tagged definitions to resolve references
  # to already supplied methods. Expose only the actual selected helper bodies;
  # no definition or equation is replaced and a genuine cycle still fails.
  def install!(audit, translation, output) do
    helpers =
      Enum.filter(
        translation["functions"],
        &(&1["rust_name"] ==
            "alloc::io::read::default_read_exact" and &1["is_opaque"] == false)
      )

    for helper <- helpers do
      function = Enum.find(audit.functions, &(&1["def_id"] == helper["def_id"]))

      unless function && selected?(function, audit.translated),
        do: raise(ArgumentError, "exact-read helper implementation correspondence mismatch")

      path = Path.join(output, helper["lean_file"])
      relative = String.replace_prefix(helper["lean_name"], translation["crate"] <> ".", "")

      pattern =
        Regex.compile!("(@\\[[^\\]]*)(\\]\\s*\\ndef " <> Regex.escape(relative) <> "(?=\\s|:))")

      source = File.read!(path)

      unless length(Regex.scan(pattern, source)) == 1,
        do:
          raise(
            ArgumentError,
            "unsupported exact-read helper declaration: #{helper["lean_name"]}"
          )

      source =
        Regex.replace(pattern, source, fn _, attributes, tail ->
          attributes <> ", trait_default" <> tail
        end)

      File.write!(path, source)
    end

    :ok
  end

  def static_error_reference?(
        %{"kind" => %{"Global" => %{"id" => id, "generics" => args}}, "ty" => type},
        translated,
        refs
      ) do
    case Enum.filter(translated["global_decls"], &(&1 && &1["def_id"] == id)) do
      [global] ->
        args == ResourceModels.args([]) and
          constant?(global, refs, translated["type_decls"]) and
          CallModels.expand(global["ty"], refs) == CallModels.expand(type, refs)

      _ ->
        false
    end
  end

  def static_error_reference?(_, _, _), do: false

  # Link dictionary parameters to matching caller clauses or the actual checked
  # File::read external model. No first-party reader is supplied by a contract.
  def audit(functions, models, translated, refs) do
    ctx = %{
      functions: Map.new(functions, &{&1["def_id"], &1}),
      models: models,
      translated: translated,
      refs: refs,
      traits: ResourceModels.trait_references(translated),
      read:
        Enum.find(
          translated["trait_decls"] || [],
          &(&1 && &1["item_meta"]["name"] == path(~w(alloc io read Read)))
        )
    }

    Enum.reduce_while(functions, {:ok, %{dependencies: %{}, calls: %{}}}, fn function,
                                                                             {:ok, result} ->
      try do
        {deps, calls} = walk(function["body"], function, ctx)

        {:cont,
         {:ok,
          %{
            dependencies: Map.put(result.dependencies, function["def_id"], Enum.uniq(deps)),
            calls: Map.put(result.calls, function["def_id"], Enum.uniq(calls))
          }}}
      rescue
        error in ArgumentError -> {:halt, {:error, function, Exception.message(error)}}
      end
    end)
  end

  defp walk(%{"Call" => %{"call" => %{"func" => func}}} = node, owner, ctx) do
    {deps, calls} = call(func, owner, ctx)
    {nested, more} = walk(Map.values(node), owner, ctx)
    {deps ++ nested, calls ++ more}
  end

  defp walk(node, owner, ctx) when is_map(node), do: walk(Map.values(node), owner, ctx)

  defp walk(nodes, owner, ctx) when is_list(nodes),
    do:
      Enum.reduce(nodes, {[], []}, fn node, {deps, calls} ->
        {more, nested} = walk(node, owner, ctx)
        {deps ++ more, calls ++ nested}
      end)

  defp walk(_, _, _), do: {[], []}

  defp call(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}, owner, ctx) do
    target = ctx.functions[id]

    if target && ctx.read do
      deps =
        for {bound, index} <- Enum.with_index(target["generics"]["trait_clauses"]),
            expected = clause(bound, ctx),
            expected["id"] == ctx.read["def_id"],
            reduce: [] do
          deps ->
            require!(length(args["trait_refs"]) == length(target["generics"]["trait_clauses"]))
            expected = substitute(expected, CallModels.expand(args["types"], ctx.refs))

            deps ++
              dictionary!(
                ResourceModels.dictionary(Enum.at(args["trait_refs"], index), ctx.traits),
                expected,
                owner,
                ctx
              )
        end

      {deps, []}
    else
      {[], []}
    end
  end

  defp call(
         %{"Regular" => %{"kind" => %{"Trait" => [raw, 0]}, "generics" => args}} = func,
         owner,
         ctx
       ) do
    value =
      ResourceModels.dictionary(
        %{"regions" => [], "outlives" => [], "skip_binder" => raw},
        ctx.traits
      )

    if ctx.read && value && value["trait_decl_ref"]["id"] == ctx.read["def_id"] do
      require!(
        length(args["regions"]) == 2 and
          Enum.all?(~w(types const_generics trait_refs), &(args[&1] == []))
      )

      deps = dictionary!(value, CallModels.expand(value["trait_decl_ref"], ctx.refs), owner, ctx)
      {deps, [func]}
    else
      {[], []}
    end
  end

  defp call(_, _, _), do: {[], []}

  defp dictionary!(%{"trait_decl_ref" => actual, "kind" => kind}, expected, owner, ctx) do
    require!(CallModels.expand(actual, ctx.refs) == expected)

    case kind do
      %{"Clause" => [%{"Free" => index}, %{"regions" => []}]} ->
        bound = Enum.find(owner["generics"]["trait_clauses"], &(&1["clause_id"] == index))
        require!(bound && clause(bound, ctx) == expected)
        []

      "SelfId" ->
        require!(Enum.any?(owner["generics"]["trait_clauses"], &(clause(&1, ctx) == expected)))
        trait = ctx.read["def_id"]

        require!(
          match?(
            %{"TraitDefault" => %{"trait_ref" => %{"id" => ^trait}}},
            owner["src"]
          )
        )

        []

      %{"TraitImpl" => %{"id" => id, "generics" => args}} ->
        impl = Enum.find(ctx.translated["trait_impls"], &(&1 && &1["def_id"] == id))
        require!(impl && impl["src"] == "Normal" && !impl["is_negative"] && !impl["is_unsafe"])

        require!(
          args == ResourceModels.args([]) and
            Enum.all?(
              ~w(regions types const_generics trait_clauses outlives trait_type_constraints),
              &(impl["generics"][&1] == [])
            )
        )

        require!(CallModels.expand(impl["impl_trait"], ctx.refs) == expected)

        methods =
          Enum.filter(
            impl["methods"],
            &(&1 && &1["kind"] == %{"TraitMethod" => [ctx.read["def_id"], 0]})
          )

        require!(length(methods) == 1)
        [method] = methods

        id = method["skip_binder"]["id"]
        function = Enum.find(ctx.translated["fun_decls"], &(&1 && &1["def_id"] == id))
        model = function && FileModels.resolve(function, ctx.translated, ctx.refs)
        require!(get_in(function, ["src", "TraitImpl", "impl_ref", "id"]) == impl["def_id"])

        require!(
          model && ctx.models[id] && model.lean == "Lynx.NativeFile.read" &&
            ctx.models[id].lean == model.lean
        )

        [id]

      _ ->
        require!(false)
    end
  end

  defp dictionary!(_, _, _, _), do: require!(false)
  defp clause(bound, ctx), do: CallModels.expand(bound["trait_"]["skip_binder"], ctx.refs)
  defp substitute(%{"TypeVar" => %{"Free" => index}}, types), do: Enum.fetch!(types, index)

  defp substitute(map, types) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, substitute(v, types)} end)

  defp substitute(list, types) when is_list(list), do: Enum.map(list, &substitute(&1, types))
  defp substitute(value, _), do: value
  defp require!(true), do: :ok

  defp require!(_),
    do:
      raise(
        ArgumentError,
        "missing or inconsistent Read dictionary; requires a matching generic clause or the audited standard File::read model"
      )

  def global?(global, translated, refs) do
    constant?(global, refs, translated["type_decls"]) or
      case Enum.reverse(global["item_meta"]["name"]) do
        [%{"Builtin" => ["PromotedConst", _]} | rest] ->
          global["global_kind"] == "AnonConst" and
            constant_name?(Enum.reverse(rest), refs, translated["type_decls"])

        _ ->
          false
      end
  end

  def constant?(global, refs, types) do
    global["src"] == "Normal" and global["global_kind"] == "NamedConst" and
      constant_name?(global["item_meta"]["name"], refs, types) and
      case error(types) do
        %{"def_id" => id} -> CallModels.expand(global["ty"], refs) == adt(id)
        _ -> false
      end
  end

  defp constant_name?(
         [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["io", 0]},
           %{"Ident" => ["error", 0]},
           %{
             "Impl" => %{
               "Ty" => %{
                 "kind" => "InherentImplBlock",
                 "params" => params,
                 "skip_binder" => parent
               }
             }
           },
           %{"Ident" => ["READ_EXACT_EOF", 0]}
         ],
         refs,
         types
       ) do
    case error(types) do
      %{"def_id" => id} ->
        Enum.all?(
          ~w(regions types const_generics trait_clauses outlives trait_type_constraints),
          &(params[&1] == [])
        ) and CallModels.expand(parent, refs) == adt(id)

      _ ->
        false
    end
  end

  defp constant_name?(_, _, _), do: false

  defp reader?(function, translated, refs) do
    with %{
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "generics" => params
         } <- function,
         [%{"index" => 0}, %{"index" => 1}] <- params["regions"],
         [%{"index" => 0}] <- params["types"],
         true <- params["const_generics"] == [] and params["trait_type_constraints"] == [],
         [clause] <- params["trait_clauses"],
         true <- clause["clause_id"] == 0,
         %{
           "regions" => [],
           "outlives" => [],
           "skip_binder" => %{"id" => trait, "generics" => args}
         } <- CallModels.expand(clause["trait_"], refs),
         true <- args == ResourceModels.args([variable()]),
         [declaration] <- Enum.filter(translated["trait_decls"], &(&1 && &1["def_id"] == trait)),
         true <- declaration["item_meta"]["name"] == path(~w(alloc io read Read)),
         %{"def_id" => error} <- FileModels.error_declaration(translated),
         [result] <-
           Enum.filter(
             translated["type_decls"],
             &(&1 && &1["item_meta"]["name"] == path(~w(core result Result)))
           ),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             reference(0, variable()),
             reference(1, %{"Slice" => [scalar(), nil]})
           ],
         true <-
           CallModels.expand(sig["output"], refs) == %{
             "Adt" => %{
               "id" => result["def_id"],
               "builtin" => nil,
               "generics" =>
                 ResourceModels.args([
                   %{
                     "Adt" => %{
                       "id" => 0,
                       "builtin" => "Tuple",
                       "generics" => ResourceModels.args([])
                     }
                   },
                   adt(error)
                 ])
             }
           },
         [outlives] <- CallModels.expand(params["outlives"], refs),
         true <-
           outlives == %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => [%{"Lub" => variable()}, %{"Var" => %{"Free" => 0}}]
           } do
      true
    else
      _ -> false
    end
  end

  defp default_method?(function, translated) do
    with %{"TraitDefault" => %{"trait_ref" => %{"id" => id}, "item_id" => item}} <-
           function["src"],
         [trait] <- Enum.filter(translated["trait_decls"], &(&1 && &1["def_id"] == id)),
         [method] <-
           Enum.filter(trait["methods"], &(&1["kind"] == %{"TraitMethod" => [id, item]})),
         %{"id" => function_id} <- method["skip_binder"]["default"] do
      function_id == function["def_id"] and
        method["skip_binder"]["item_meta"]["name"] == function["item_meta"]["name"]
    else
      _ -> false
    end
  end

  defp error(types),
    do: Enum.find(types, &(&1 && &1["item_meta"]["name"] == path(~w(core io error Error))))

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp adt(id),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => ResourceModels.args([])}}

  defp variable, do: %{"TypeVar" => %{"Free" => 0}}
  defp scalar, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}
  defp reference(region, type), do: %{"Ref" => [%{"Var" => %{"Free" => region}}, type, "Mut"]}
end
