defmodule Lynx.External do
  @moduledoc """
  An external implementation bundle supplied by a translation backend.

  `bindings` lists pure `{module, function, arity}` implementations defined by
  `files`, in the runner's input format. The backend is responsible for the
  correspondence to the external program and for preparing its Lean dependencies.
  Registration alone does not establish that correspondence. Lynx checks the
  resulting Elixir laws and their transitive axiom dependencies as usual.
  Every external input module is also audited in full, including unused and
  private declarations. Backends can include `"audit_modules"` in input files
  to audit imported implementation and proof modules in the same way.

  `fingerprint` optionally identifies the freshly extracted external program and
  its build inputs with a lowercase SHA-256 digest. A backend must recompute this
  before verification; it is not a reusable registration token. Bundles without
  fingerprints and their dependent laws bypass persistent verification caching.
  Actual transitive Lean implementation/proof artifacts also enter runner cache
  keys, independently of this backend fingerprint.

  `implementation_modules` optionally maps BEAM modules to the Lean input module
  providing their bindings. Declarations retain their ordinary BEAM namespace.
  `native_exports` maps BEAM modules to their complete compiled native export
  lists (`{function, arity}` pairs), including unselected exports. A backend must
  validate this inventory against the configured native artifact. With an
  inventory, ordinary helpers in that module can be translated; unregistered
  native exports still fail. Without one the entire module remains external.

  Native backends used through `native: {backend, options}` export `prepare!/1`
  and return an external bundle, its Lake `:project`, and a `:verification` summary.
  Prefer that workflow for mutable workspaces: preparation and law checking hold
  one Mix OS concurrency lock. A manually prepared bundle must be consumed before
  another extraction overwrites its module namespace.
  """

  @enforce_keys [:bindings, :files]
  defstruct [:bindings, :files, :fingerprint, implementation_modules: %{}, native_exports: %{}]
  @doc false
  def with_native_lock(opts, fun) do
    if opts[:native], do: with_preparation_lock(fun), else: fun.()
  end

  @doc false
  def with_preparation_lock(fun) do
    unless Code.ensure_loaded?(Mix.Sync.Lock) && function_exported?(Mix.Sync.Lock, :with_lock, 2),
      do: raise(ArgumentError, "native verification requires Mix.Sync.Lock support")

    if System.get_env("MIX_OS_CONCURRENCY_LOCK") in ["0", "false"],
      do: raise(ArgumentError, "native verification requires Mix OS concurrency locking")

    # Mix's reentrant lock covers both BEAM processes and separate Mix invocations.
    Mix.Sync.Lock.with_lock("lynx-native-verification-v1", fun)
  end

  @doc false
  def prepare_options!(opts) do
    case Keyword.pop(opts, :native) do
      {nil, opts} ->
        {opts, nil}

      {{backend, config}, opts} when is_atom(backend) and is_list(config) ->
        unless Code.ensure_loaded?(backend) && function_exported?(backend, :prepare!, 1),
          do: raise(ArgumentError, "native backend must export prepare!/1: #{inspect(backend)}")

        %{external: %__MODULE__{} = external, project: project, verification: verification} =
          backend.prepare!(config)

        if opts[:lean_project] && Path.expand(opts[:lean_project]) != project,
          do: raise(ArgumentError, "native backend and laws must use the same Lean project")

        opts =
          opts
          |> Keyword.put(:lean_project, project)
          |> Keyword.update(:externals, [external], &[external | &1])

        {opts, verification}

      {other, _} ->
        raise ArgumentError,
              "native verification must be {backend, keyword_options}, got: #{inspect(other)}"
    end
  end

  @doc false
  def attach_guarantees(reports, _files, nil), do: reports

  def attach_guarantees(reports, files, verification) do
    by_module = Map.new(files, &{&1["module"], &1})

    Enum.map(reports, fn report ->
      guarantees =
        if report.module == verification.report_module,
          do:
            Enum.map(
              verification.guarantees,
              fn row ->
                row
                |> Map.put(:status, if(report.status == :ok, do: :verified, else: report.status))
                |> Map.update!(:label, fn label ->
                  if report.status == :ok,
                    do: label,
                    else: String.replace(label, " verified", " not verified")
                end)
              end
            ),
          else: []

      laws =
        for %{"kind" => "theorem", "name" => name, "params" => params} <-
              by_module[report.module]["contents"] do
          %{
            kind: :elixir_law,
            label:
              if(report.status == :ok, do: "Elixir law verified", else: "Elixir law not verified"),
            status: if(report.status == :ok, do: :verified, else: report.status),
            module: report.module,
            theorem: "#{name}/#{length(params)}",
            file: report.file
          }
        end

      if guarantees == [] && laws == [],
        do: report,
        else:
          Map.merge(report, %{
            guarantees: guarantees ++ laws,
            trusted_boundary: verification.trusted_boundary,
            external_models: verification.external_models,
            unverified_external_calls: verification.unverified_external_calls,
            unverified_nif_exports: Map.get(verification, :unverified_nif_exports, [])
          })
    end)
  end
end
