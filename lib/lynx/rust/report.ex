defmodule Lynx.Rust.Report do
  @moduledoc """
  Evidence about freshly extracted Rust implementations and their checked properties.

  A successful extraction is labelled `:extracted`, not `:verified`. A verified
  property records its actual Lean theorem statement and the implementations
  mentioned in that statement. Cross-crate rows also identify the extracted
  callees and checked contracts used by the proof. This is verification under
  extracted semantics, not a proof about native machine code or the FFI.
  """

  @trusted [
    "Rust compiler, Charon and Aeneas extraction",
    "reproducible Cargo build scripts and procedural macros",
    "Lean kernel; propext, Classical.choice and Quot.sound"
  ]

  @doc false
  def build!(extraction, reports, opts \\ []) do
    unless Enum.all?(reports, &(&1.status == :ok)),
      do: raise(ArgumentError, "cannot report failed Rust proofs as verified")

    properties = Lynx.Rust.Proofs.properties!(reports)
    models = extraction.implementations

    by_name =
      Map.new(models, fn {_id, implementation} ->
        {implementation["lean_name"], implementation}
      end)

    dependencies = Lynx.Rust.LLBC.dependencies(extraction.audit)

    external =
      Map.new(extraction.audit.external_calls, fn {id, model} ->
        {id,
         Map.take(model, [
           :definition_id,
           :rust_name,
           :lean,
           :label,
           :status,
           :implementation_verified
         ])}
      end)

    constants = Map.get(extraction, :constants, %{})

    initializer_names =
      Map.new(constants, fn {_id, model} ->
        {Lynx.Rust.Constants.initializer_id(model["declaration"]), model["rust_name"]}
      end)

    directory = Keyword.fetch!(opts, :source_dir)

    implementations =
      for implementation <- Map.values(models) do
        source = implementation["source"] || %{}

        %{
          rust_name: implementation["rust_name"],
          lean_name: implementation["lean_name"],
          definition_id: implementation["def_id"],
          status: :extracted,
          file:
            if(is_binary(source["file"]), do: Path.expand(source["file"], directory), else: nil),
          line: source["begin_line"],
          dependencies:
            Enum.map(dependencies[implementation["def_id"]], fn id ->
              cond do
                models[id] -> models[id]["rust_name"]
                external[id] -> external[id].rust_name
                true -> Map.fetch!(initializer_names, id)
              end
            end),
          external_dependencies:
            external_dependencies(implementation["def_id"], dependencies, external, MapSet.new())
        }
      end
      |> Enum.sort_by(& &1.rust_name)

    verified =
      for property <- properties, lean_name <- property["implementations"] do
        implementation = Map.fetch!(by_name, lean_name)
        source = Enum.find(implementations, &(&1.lean_name == lean_name))

        Map.merge(source, %{
          kind: :rust_implementation,
          status: :verified,
          label: "Rust implementation verified",
          theorem: property["theorem"],
          statement: property["statement"],
          contracts_used: property["contracts_used"],
          implementation_dependencies:
            dependencies[implementation["def_id"]]
            |> Enum.filter(&Map.has_key?(models, &1))
            |> Enum.map(&Map.fetch!(models, &1))
        })
      end

    composed =
      for property <- verified,
          callees =
            Enum.filter(
              property.implementation_dependencies,
              &(crate(&1["rust_name"]) != crate(property.rust_name))
            ),
          callees != [] do
        %{
          property
          | kind: :cross_crate_contract,
            label: "Cross-crate contract verified",
            implementation_dependencies:
              Enum.map(callees, &Map.take(&1, ~w(def_id rust_name lean_name)))
        }
      end

    verified =
      Enum.map(
        verified,
        fn property ->
          Map.update!(property, :implementation_dependencies, fn callees ->
            Enum.map(callees, &Map.take(&1, ~w(def_id rust_name lean_name)))
          end)
        end
      )

    verified = Enum.sort_by(verified, &{&1.rust_name, &1.theorem})
    composed = Enum.sort_by(composed, &{&1.rust_name, &1.theorem})

    %{
      report_module: List.last(reports).module,
      implementations: implementations,
      constants:
        constants
        |> Map.values()
        |> Enum.map(fn model ->
          model
          |> Map.take(~w(def_id rust_name lean_name lean_file can_fail source initializer_id))
          |> Map.put("status", if(model["inlined"], do: :inlined, else: :extracted))
        end)
        |> Enum.sort_by(& &1["rust_name"]),
      guarantees: verified ++ composed,
      properties: properties,
      fingerprint: extraction.fingerprint,
      trusted_boundary: @trusted,
      external_models:
        ["Aeneas bounded scalar operations and RustM computation model"] ++
          Enum.map(Map.get(extraction, :external_types, []), & &1.label) ++
          Enum.map(Map.values(external), & &1.label) ++
          if(
            Enum.any?(extraction.audit.translated["type_decls"], fn
              %{
                "item_meta" => %{
                  "name" => [
                    %{"Ident" => ["core", 0]},
                    %{"Ident" => ["result", 0]},
                    %{"Ident" => ["Result", 0]}
                  ]
                }
              } ->
                true

              _ ->
                false
            end),
            do: [
              "Aeneas core::result::Result data representation; standard enum definition extracted"
            ],
            else: []
          ),
      unverified_external_calls: external |> Map.values() |> Enum.sort_by(& &1.rust_name),
      cutoff: "divergence and undef are uncatchable verification exhaustion"
    }
  end

  @doc false
  def rustler(report, bindings, version) do
    module = :lynx_core_to_leanj.module_name(String.to_atom(bindings.module))

    adapters =
      for binding <- bindings.bindings do
        %{
          kind: :nif_adapter,
          label: "NIF adapter verified",
          status: :verified,
          module: bindings.module,
          function: binding["name"],
          arity: binding["arity"],
          scheduler: binding["flags"],
          arguments: binding["arguments"],
          result: binding["result"],
          lean_name: binding["lean_name"],
          theorem: module <> ".«#{binding["name"]}:adapter/#{binding["arity"]}»",
          statement: "modelled decoder, extracted computation and encoder correspondence"
        }
      end

    unverified =
      for {name, arity, scheduler} <- bindings.exports,
          not Enum.any?(bindings.bindings, &(&1["name"] == name && &1["arity"] == arity)) do
        %{
          module: bindings.module,
          function: name,
          arity: arity,
          scheduler: scheduler,
          status: :unverified,
          reason: "not selected for verification"
        }
      end

    %{
      report
      | guarantees: report.guarantees ++ adapters,
        trusted_boundary:
          report.trusted_boundary ++
            [
              "Rustler #{version} wrapper, unsafe FFI, native code and BEAM NIF API",
              "configured native artifact is installed by the application loader"
            ]
    }
    |> Map.put(:rustler_version, version)
    |> Map.put(:unverified_nif_exports, unverified)
  end

  defp crate(name), do: name |> String.split("::") |> hd()

  defp external_dependencies(id, dependencies, external, seen) do
    if MapSet.member?(seen, id) do
      []
    else
      seen = MapSet.put(seen, id)

      for callee <- Map.fetch!(dependencies, id),
          model <-
            if(Map.has_key?(external, callee),
              do: [external[callee]],
              else: external_dependencies(callee, dependencies, external, seen)
            ),
          do: model
    end
    |> Enum.uniq_by(& &1.definition_id)
    |> Enum.sort_by(& &1.rust_name)
  end
end
