defmodule Lynx.Rust.Proofs do
  @moduledoc false
  @marker "LYNX_RUST_PROPERTIES:"

  # Lean discovers theorem statements, rather than trusting per-function labels.
  # The report is consumed only after the normal full-module axiom audit succeeds.
  def file!(extraction, proof_modules, opts \\ []) do
    name = Keyword.get(opts, :module, extraction.module <> ".Verification")

    imports =
      Enum.uniq([extraction.module <> ".Funs" | proof_modules ++ Keyword.get(opts, :imports, [])])

    implementations =
      extraction.implementations |> Map.values() |> Enum.map(& &1["lean_name"]) |> Enum.sort()

    required = Keyword.get(opts, :required_properties, [])

    source = """
    module
    #{Enum.map_join(imports, "\n", &("public import " <> identifier!(&1)))}
    open Lean Elab Command
    private meta def inspectRustProperties : CommandElabM Unit := do
      let proofModules : Array Name := #{names(proof_modules)}
      let imports := proofModules.map fun moduleName =>
        { module := moduleName, importAll := true, isExported := false : Import }
      unsafe enableInitializersExecution
      let auditEnv ← importModules imports {} (loadExts := true)
      let properties ← withEnv auditEnv do
        let env := auditEnv.setExporting false
        let implementations : Array Name := #{names(implementations)}
        let required : Array Name := #{names(required)}
        let mut found : Array Name := #[]
        let mut properties : Array Json := #[]
        for entry in env.constants.toList do
          let declName := entry.1
          let some moduleIdx := env.getModuleIdxFor? declName | continue
          unless proofModules.contains env.header.moduleNames[moduleIdx.toNat]! do continue
          let some info := env.find? declName | continue
          let .thmInfo proof := info | continue
          unless required.contains declName || (← findDeclarationRanges? declName).isSome do continue
          let targets := implementations.filter proof.type.getUsedConstants.contains
          if targets.isEmpty then continue
          let proposition ← liftTermElabM do pure (toString (← Meta.ppExpr proof.type))
          let contracts := proof.value.getUsedConstants.filter fun dependency => Id.run do
            let some (.thmInfo _) := env.find? dependency | return false
            let some index := env.getModuleIdxFor? dependency | return false
            return proofModules.contains env.header.moduleNames[index.toNat]!
          found := found.push declName
          properties := properties.push (Json.mkObj [
            ("theorem", toJson declName.toString), ("statement", toJson proposition),
            ("implementations", toJson (targets.map toString)),
            ("contracts_used", toJson (contracts.map toString))])
        for declName in required do
          unless found.contains declName do
            throwError "required Rust property is missing, is not a theorem, or has no extracted implementation in its statement: {declName}"
        return properties
      logInfo (#{JSON.encode!(@marker)} ++ (Json.arr properties).compress)
    run_cmd inspectRustProperties
    """

    %{
      "module" => name,
      "file" => name <> ".lean",
      "imports" => imports,
      "contents" => [],
      "audit_modules" => Enum.uniq([name | imports] ++ Map.get(extraction, :model_modules, [])),
      "preludes" => [
        %{"source" => source, "file" => name <> ".lean", "span" => [1], "indentation" => 0}
      ]
    }
  end

  def properties!(reports) do
    messages =
      for %{status: :ok, diagnostics: diagnostics} <- reports,
          %{severity: :information, message: @marker <> json} <- diagnostics,
          do: JSON.decode!(json)

    case messages do
      [properties] -> properties
      _ -> raise "missing or ambiguous checked Rust property report"
    end
  end

  defp names(names),
    do: "#[" <> Enum.map_join(names, ", ", &(JSON.encode!(&1) <> ".toName")) <> "]"

  defp identifier!(name) do
    name
    |> String.split(".")
    |> Enum.map_join(".", fn part ->
      if String.contains?(part, ["«", "»", "\n", "\r"]),
        do: raise(ArgumentError, "unsupported Lean module name")

      "«" <> part <> "»"
    end)
  end
end
