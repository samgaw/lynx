defmodule Lynx.Rust.NoPanic do
  @moduledoc false
  alias Lynx.Rust.LLBC

  # These are pending obligations, never assumed external implementations.
  # The caller's cleanup may be provisionally reduced, but the helper and every
  # implementation dependency are protected from that reduction. Proofs.file!
  # kernel-checks the precise all-input outcome before verification can succeed.
  def validate!(opts) do
    contracts = Keyword.get(opts, :nonpanicking, [])

    unless is_list(contracts) and
             Enum.all?(contracts, fn
               {rust, theorem} when is_binary(rust) and is_binary(theorem) ->
                 Regex.match?(~r/\A[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)+\z/, rust) and
                   Regex.match?(
                     ~r/\A[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)+\z/,
                     theorem
                   )

               _ ->
                 false
             end) and length(contracts) == length(Enum.uniq_by(contracts, &elem(&1, 0))),
           do:
             raise(
               ArgumentError,
               "nonpanicking requires unique {Rust function, Lean theorem} pairs"
             )

    if contracts != [] and
         (Keyword.get(opts, :execution, :pure) != :runtime or
            Keyword.get(opts, :unwind, :reject) not in [:reject, :captured]),
       do:
         raise(
           ArgumentError,
           "nonpanicking proofs require runtime execution with unwind: :reject or :captured"
         )

    :ok
  end

  def prepare!(document, [], _first_party),
    do: {document, %{contracts: [], protected: MapSet.new()}}

  def prepare!(document, contracts, first_party) do
    translated =
      document
      |> Lynx.Rust.LLBCJson.restore_trait_references!(document)
      |> Map.fetch!("translated")

    functions =
      Map.new(for f <- translated["fun_decls"], f != nil, do: {f["def_id"], f})

    selected =
      for {rust, theorem} <- contracts do
        matches =
          for {id, f} <- functions,
              name(f) == rust,
              hd(String.split(rust, "::")) in first_party,
              do: {id, f}

        case matches do
          [{id, %{"body" => %{"Structured" => _}, "src" => "Normal"}}] ->
            %{id: id, rust: rust, theorem: theorem}

          _ ->
            raise ArgumentError,
                  "nonpanicking proof requires an extracted ordinary first-party implementation: #{rust}"
        end
      end

    initializers =
      Map.new(Enum.reject(translated["global_decls"] || [], &is_nil/1), fn global ->
        {global["def_id"], Lynx.Rust.Constants.initializer_id(global)}
      end)

    dictionaries =
      Map.new(Enum.reject(translated["trait_impls"] || [], &is_nil/1), &{&1["def_id"], &1})

    dependencies =
      Map.new(functions, fn {id, f} ->
        {id,
         references(f["body"]) ++
           global_references(f["body"], initializers) ++
           dictionary_references(f["body"], dictionaries, initializers, MapSet.new())}
      end)

    protected = closure(Enum.map(selected, & &1.id), dependencies, MapSet.new())

    {document, %{contracts: selected, protected: protected}}
  end

  # Resolved callbacks, trait dispatch, and constant initializers must not add a
  # hidden implementation dependency outside the protected original call graph.
  # Such cases fail closed rather than permitting circular cleanup justification.
  def audit!(plan, audit) do
    dependencies = LLBC.dependencies(audit)
    required = closure(Enum.map(plan.contracts, & &1.id), dependencies, MapSet.new())

    implementations =
      MapSet.new(audit.functions ++ Map.get(audit, :constant_initializers, []), & &1["def_id"])

    missing =
      required |> MapSet.intersection(implementations) |> MapSet.difference(plan.protected)

    if MapSet.size(missing) != 0,
      do:
        raise(
          ArgumentError,
          "nonpanicking proof has unsupported indirect implementation dependencies"
        )

    :ok
  end

  def link!(plan, implementations) do
    for contract <- plan.contracts do
      implementation = Map.fetch!(implementations, contract.id)

      unless implementation["rust_name"] == contract.rust,
        do: raise(ArgumentError, "nonpanicking implementation identity mismatch")

      Map.put(contract, :lean, implementation["lean_name"])
    end
  end

  def checks_source([]), do: ""

  def checks_source(contracts) do
    checks =
      contracts
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {contract, index} ->
        """
        run_cmd checkNativeNoPanic #{JSON.encode!(contract.lean)}.toName #{JSON.encode!(contract.theorem)}.toName #{JSON.encode!("checkNativeNoPanic#{index}")}.toName
        """
      end)

    """
    private meta def checkNativeNoPanic (implementation certificate declaration : Name) : CommandElabM Unit := do
      let expected ← liftTermElabM do
        let info ← getConstInfo implementation
        Meta.forallTelescope info.type fun inputs resultType => do
          let .app (.const ``Lynx.Result _) _ ← Meta.whnf resultType
            | throwError "nonpanicking implementation must return NativeM: {implementation}"
          let call := mkAppN (mkConst implementation) inputs
          let safe ← Meta.mkAppM ``Lynx.NativeM.NoPanic #[call]
          PrettyPrinter.delab (← Meta.mkForallFVars inputs safe)
      let command ← `(command| private theorem $(mkIdent declaration) : $expected := by
        intros
        first
        | apply $(mkIdent certificate)
        | apply Lynx.NativeM.NoPanic.of_pure
          apply $(mkIdent certificate))
      elabCommand command
    #{checks}
    """
  end

  defp name(function) do
    parts = function["item_meta"]["name"]

    if Enum.all?(parts, &match?(%{"Ident" => [_, _]}, &1)),
      do: Enum.map_join(parts, "::", fn %{"Ident" => [part, _]} -> part end)
  end

  defp references(%{"Fun" => id}) when is_integer(id), do: [id]
  defp references(map) when is_map(map), do: Enum.flat_map(Map.values(map), &references/1)
  defp references(list) when is_list(list), do: Enum.flat_map(list, &references/1)
  defp references(_), do: []

  # Compiler-resolved dictionaries can invoke closure methods without a direct
  # function operand at the call site. Protect every method and inherited
  # dictionary dependency before any pending certificate can prune cleanup.
  defp dictionary_references(
         %{"TraitImpl" => %{"id" => id}} = node,
         dictionaries,
         initializers,
         seen
       ) do
    visited = MapSet.member?(seen, id)
    seen = MapSet.put(seen, id)
    children = dictionary_references(Map.values(node), dictionaries, initializers, seen)

    if visited do
      children
    else
      dictionary = Map.get(dictionaries, id, %{})
      nested = Map.take(dictionary, ~w(methods implied_trait_refs consts))

      methods =
        for %{"skip_binder" => %{"id" => method}} <- dictionary["methods"] || [], do: method

      children ++
        methods ++
        references(nested) ++
        global_references(nested, initializers) ++
        dictionary_references(nested, dictionaries, initializers, seen)
    end
  end

  defp dictionary_references(node, dictionaries, initializers, seen) when is_map(node),
    do: dictionary_references(Map.values(node), dictionaries, initializers, seen)

  defp dictionary_references(nodes, dictionaries, initializers, seen) when is_list(nodes),
    do: Enum.flat_map(nodes, &dictionary_references(&1, dictionaries, initializers, seen))

  defp dictionary_references(_, _, _, _), do: []

  # A const read executes its actual initializer. Protect that body and its
  # dependencies before any pending certificate can simplify unwind cleanup.
  defp global_references(%{"Global" => %{"id" => id}} = node, initializers),
    do: List.wrap(initializers[id]) ++ global_references(Map.values(node), initializers)

  defp global_references(node, initializers) when is_map(node),
    do: global_references(Map.values(node), initializers)

  defp global_references(nodes, initializers) when is_list(nodes),
    do: Enum.flat_map(nodes, &global_references(&1, initializers))

  defp global_references(_, _), do: []

  defp closure([], _, seen), do: seen

  defp closure([id | rest], graph, seen) do
    if MapSet.member?(seen, id),
      do: closure(rest, graph, seen),
      else: closure(Map.get(graph, id, []) ++ rest, graph, MapSet.put(seen, id))
  end
end
