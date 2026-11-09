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
           :implementation_verified,
           :native_cutoff_only,
           :native_wake_operation
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
          source_kind:
            if(implementation["def_id"] in extraction.audit.library_helpers,
              do: :included_library_helper,
              else: :workspace
            ),
          file:
            if(is_binary(source["file"]), do: Path.expand(source["file"], directory), else: nil),
          line: source["begin_line"],
          drop_effects: Map.get(extraction.audit.drops.sites, implementation["def_id"], []),
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
              implementation_dependencies(property.definition_id, dependencies, models),
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
      execution: Map.get(extraction, :execution, :pure),
      implementations: implementations,
      verification_bounds:
        if(
          Map.get(extraction, :execution, :pure) == :runtime and
            Enum.any?(Map.values(models), &(&1["loop_helpers"] not in [nil, []])),
          do: [%{kind: :native_loop, iterations: 262_145, exhausted: :verification_cutoff}],
          else: []
        ),
      constants:
        constants
        |> Map.values()
        |> Enum.map(fn model ->
          model
          |> Map.take(
            ~w(def_id rust_name lean_name lean_file can_fail source initializer_id implementation_verified)
          )
          |> Map.put(
            "status",
            cond do
              model["modelled"] -> :modelled
              model["inlined"] -> :inlined
              true -> :extracted
            end
          )
        end)
        |> Enum.sort_by(& &1["rust_name"]),
      guarantees: verified ++ composed,
      properties: properties,
      fingerprint: extraction.fingerprint,
      trusted_boundary:
        @trusted ++
          if(Enum.any?(Map.values(extraction.audit.external_calls), & &1[:native_wake_operation]),
            do: [
              "Registered nonpanicking wake callback relation; native Context/Waker registration, vtables, allocation and executor correctness unverified"
            ],
            else: []
          ) ++
          if(Map.get(extraction, :native_unwind, []) != [],
            do: [
              "Lynx validated native cleanup, constant drop-flag lowering and nonpanicking-call analysis"
            ],
            else: []
          ) ++
          if(Map.get(extraction, :native_drops, []) != [],
            do: ["Lynx audited owned-place consuming-drop lowering to core::mem::drop"],
            else: []
          ) ++
          if(map_size(extraction.audit.drops.erasures) > 0,
            do: ["Lynx compiler-generated structural drop erasure audit"],
            else: []
          ),
      compiler_drop_queries: Map.get(extraction, :compiler_drop_queries, []),
      native_drop_lowering: Map.get(extraction, :native_drops, []),
      native_guard_storage: Map.get(extraction, :native_guard_storage, []),
      native_unwind_lowering: Map.get(extraction, :native_unwind, []),
      unwind: Map.get(extraction, :unwind, :reject),
      files: Map.get(extraction, :files, :reject),
      futures: Map.get(extraction, :futures, :reject),
      owned_drops: Map.get(extraction, :owned_drops, false),
      resource_cleanup: Map.get(extraction, :resource_cleanup, []),
      structural_drops: Lynx.Rust.DropModels.report(extraction.audit.drops),
      external_models:
        ["Aeneas bounded scalar operations and RustM computation model"] ++
          if(Map.get(extraction, :futures, :reject) in [:polling, :suspending, :cancelling],
            do: [
              "Checked standard Pin<&mut T>::as_mut reborrow lowering; standard mutable-reference DerefMut semantics, Rust memory safety and physical pinning remain trusted; custom pointer families are not admitted by this rule"
            ],
            else: []
          ) ++
          if(Map.get(extraction, :owned_drops, false),
            do: [
              "Compiler-generated owning ADT destruction: actual optimized rustc drop MIR with checked self-pointer erasure; admitted native field destructors remain explicit models; native layout, allocation and FFI correctness unverified"
            ],
            else: []
          ) ++
          if(Map.get(extraction, :futures, :reject) == :suspending,
            do: [
              "Compiler coroutine saved-slot interpretation; only drop-free Unpin saved fields; physical pinning, cancellation cleanup and executor behavior unverified"
            ],
            else: []
          ) ++
          if(Map.get(extraction, :futures, :reject) == :cancelling,
            do: [
              "Compiler coroutine saved-slot and owned destruction interpretation; actual rustc drop MIR with checked pointer erasure and valid-state guards; optional initial capture slots and saved-field transfer; one Unpin native owner per state; Aeneas replacement primitive; native destructors, allocation, physical pinning, FFI, cancellation delivery and native executor correspondence remain modeled boundaries; optional logical task execution uses atomic scheduler waits"
            ],
            else: []
          ) ++
          if(Map.get(extraction, :native_guard_storage, []) != [],
            do: [
              "Saved native guard capability representation: opaque std MutexGuard lifetime arguments erased after native ownership and borrow admission; explicit guard references and actual executable bodies retained; Rust memory safety, std, OS locking and FFI remain trusted boundaries"
            ],
            else: []
          ) ++
          if(Map.get(extraction, :execution, :pure) == :runtime,
            do: [
              "Lynx resumable native interpretation: rust_panicked marker; undef/divergence exhaust verification; resource, lock, general unwind cleanup and FFI primitives require separate models"
            ],
            else: []
          ) ++
          Enum.map(Map.get(extraction, :external_types, []), & &1.label) ++
          (constants |> Map.values() |> Enum.filter(& &1["modelled"]) |> Enum.map(& &1["label"])) ++
          Enum.map(Map.values(external), & &1.label) ++
          Enum.map(Lynx.Rust.DropModels.report(extraction.audit.drops), & &1.label) ++
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

    byte_vec_model =
      "Rustler #{version} Vec<u8> codec model: sequential u32-to-u8 decoding, improper-tail panic and proper-list encoding; 1048576-element verification bound; native allocation and FFI correctness unverified"

    byte_vec? = Enum.any?(bindings.bindings, &byte_vector?([&1["arguments"], &1["result"]]))

    option_model =
      "Rustler #{version} Option codec model: payload-first decoding, nil fallback and untagged encoding; nested encodings may collide; native FFI correctness unverified"

    option? = Enum.any?(bindings.bindings, &option?([&1["arguments"], &1["result"]]))

    resource_model =
      "Rustler #{version} VM resource codec model: stable term identity, aggregate VM pin, fresh Rust owner per decode and bounded reference count; VM collection, owner death, serialization, physical reference counts and FFI correctness unverified"

    resource? = Enum.any?(bindings.bindings, &resource?([&1["arguments"], &1["result"]]))

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
          execution: Map.get(report, :execution, :pure),
          arguments: binding["arguments"],
          result: binding["result"],
          codec_models:
            if(byte_vector?([binding["arguments"], binding["result"]]),
              do: [byte_vec_model],
              else: []
            ) ++
              if(option?([binding["arguments"], binding["result"]]), do: [option_model], else: []) ++
              if(resource?([binding["arguments"], binding["result"]]),
                do: [resource_model],
                else: []
              ),
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
        external_models:
          report.external_models ++
            if(byte_vec?, do: [byte_vec_model], else: []) ++
            if(resource?, do: [resource_model], else: []) ++
            if(option?, do: [option_model], else: []),
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

  defp option?(%{"option" => _}), do: true
  defp option?(map) when is_map(map), do: Enum.any?(Map.values(map), &option?/1)
  defp option?(list) when is_list(list), do: Enum.any?(list, &option?/1)
  defp option?(_), do: false

  defp resource?(%{"resource" => _}), do: true
  defp resource?(map) when is_map(map), do: Enum.any?(Map.values(map), &resource?/1)
  defp resource?(list) when is_list(list), do: Enum.any?(list, &resource?/1)
  defp resource?(_), do: false

  defp byte_vector?(%{"vec" => "u8"}), do: true
  defp byte_vector?(map) when is_map(map), do: Enum.any?(Map.values(map), &byte_vector?/1)
  defp byte_vector?(list) when is_list(list), do: Enum.any?(list, &byte_vector?/1)
  defp byte_vector?(_), do: false

  defp crate(name), do: name |> String.split("::") |> hd()

  # Same-crate wrappers and compiler-generated poll/drop bodies can hide the
  # cross-crate call from the root's immediate callees. Follow the extracted
  # graph, stopping at external models, and retain actual implementation IDs.
  defp implementation_dependencies(root, dependencies, models) do
    dependencies
    |> Map.fetch!(root)
    |> reachable(dependencies, MapSet.new([root]))
    |> MapSet.delete(root)
    |> Enum.filter(&Map.has_key?(models, &1))
    |> Enum.map(&Map.fetch!(models, &1))
    |> Enum.sort_by(& &1["rust_name"])
  end

  defp reachable([], _dependencies, seen), do: seen

  defp reachable([id | rest], dependencies, seen) do
    if MapSet.member?(seen, id) do
      reachable(rest, dependencies, seen)
    else
      reachable(Map.get(dependencies, id, []) ++ rest, dependencies, MapSet.put(seen, id))
    end
  end

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
