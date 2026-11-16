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

  def prepare!(document, contracts, first_party) do
    translated = document["translated"]

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

    dependencies = Map.new(functions, fn {id, f} -> {id, references(f["body"])} end)
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
          let .app (.const ``Lynx.Result _) valueType ← Meta.whnf resultType
            | throwError "nonpanicking implementation must return NativeM: {implementation}"
          let call := mkAppN (mkConst implementation) inputs
          let success ← Meta.withLocalDeclD `result valueType fun value => do
            let outcome ← Meta.mkAppM ``Lynx.Result.ok #[value]
            let equal ← Meta.mkEq call outcome
            let predicate ← Meta.mkLambdaFVars #[value] equal
            Meta.mkAppM ``Exists #[predicate]
          let exhausted ← Meta.mkAppOptM ``Lynx.Result.error #[some valueType, some (mkConst ``Lynx.Exception.exhausted)]
          let failure ← Meta.mkEq call exhausted
          let outcome ← Meta.mkAppM ``Or #[success, failure]
          PrettyPrinter.delab (← Meta.mkForallFVars inputs outcome)
      let command ← `(command| private theorem $(mkIdent declaration) : $expected := $(mkIdent certificate))
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

  defp closure([], _, seen), do: seen

  defp closure([id | rest], graph, seen) do
    if MapSet.member?(seen, id),
      do: closure(rest, graph, seen),
      else: closure(Map.get(graph, id, []) ++ rest, graph, MapSet.put(seen, id))
  end
end
