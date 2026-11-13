defmodule Lynx.Rust.IoFixture do
  @moduledoc false
  @fixture Path.expand("../fixtures/rust_io", __DIR__)

  def prepare_shared!(tmp, tools, extra_modules \\ []) do
    {workspace, project, fixture} = prepare!(tmp, tools)

    for module <- fixture[:proof_modules] do
      path = Path.join(project, String.replace(module, ".", "/") <> ".lean")

      source =
        File.read!(path)
        |> String.replace("Lynx io_protocol", "Lynx io_native io_native.io_protocol")
        |> String.replace("NativeDrop.drop", "NativeOwnedDrop.drop")

      File.write!(path, source)
    end

    options = [
      workspace: workspace,
      package: "io-native",
      tools: tools,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      cargo: [features: ["shared-log"]],
      only: [log_create: 0, log_append: 2],
      proof_roots: fixture[:roots] ++ ["io_protocol::sync_directory"],
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(options)
    names = Map.new(prepared.bindings.bindings, &{&1["name"], &1["lean_name"]})

    modules =
      ~w(SharedLogProperties FramedLogProperties NativeLogProperties OverlappingLogProperties
      ScheduledLogProperties RegisteredLogProperties ContendedLogProperties ConstructorLogProperties
      ConstructedLogProperties ConstructedConcurrentProperties) ++ extra_modules

    for name <- modules do
      source =
        File.read!(Path.join(@fixture, name <> ".lean"))
        |> String.replace("__APPEND__", Map.fetch!(names, "log_append"))
        |> String.replace("__CREATE__", Map.fetch!(names, "log_create"))

      File.write!(Path.join(project, "Record/" <> name <> ".lean"), source)
    end

    properties = ~w(SharedLogProperties.facade_contract SharedLogProperties.critical_contract
      SharedLogProperties.borrow_prefix SharedLogProperties.aliasing_prefix SharedLogProperties.full_write
      FramedLogProperties.append_success FramedLogProperties.guarded_prefix
      NativeLogProperties.append_prefix NativeLogProperties.facade_prefix
      NativeLogProperties.adapter_prefix NativeLogProperties.initial_prefix
      NativeLogProperties.adapter_continuation NativeLogProperties.initial_adapter
      OverlappingLogProperties.caller_contract OverlappingLogProperties.acquired_prefix
      OverlappingLogProperties.second_call OverlappingLogProperties.overlap_phases
      ScheduledLogProperties.call_steps ScheduledLogProperties.scheduled_calls ScheduledLogProperties.scheduled_records
      RegisteredLogProperties.call_steps RegisteredLogProperties.decoded_call_steps
      ContendedLogProperties.decoded_lock_prefix ConstructorLogProperties.constructor_prefix
      ConstructedLogProperties.append_prefix ConstructedLogProperties.appended
      ConstructedConcurrentProperties.decoded_lock_prefix)

    options =
      options ++
        [
          proof_modules: Enum.map(modules, &("Record." <> &1)),
          required_properties: Enum.map(properties, &("Record." <> &1))
        ]

    %{workspace: workspace, project: project, options: options, prepared: prepared}
  end

  def prepare!(tmp, tools, extra_modules \\ []) do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Record"))

    sources =
      [
        {"Properties", [{"Disk", "Record"}]},
        {"ReadProperties",
         [
           {"Read.Properties", "Record.Properties"},
           {"Read.ReadProperties", "Record.ReadProperties"}
         ]},
        {"RecoveryProperties",
         [
           {"Recovery.Properties", "Record.Properties"},
           {"Recovery.ReadProperties", "Record.ReadProperties"},
           {"Recovery.Extraction", "Record.Extraction"},
           {"Recovery.RecoveryProperties", "Record.RecoveryProperties"}
         ]},
        {"IntegrityProperties", []},
        {"CrashProperties", []},
        {"AppendProperties", []},
        {"LogProperties", []},
        {"TailProperties", []},
        {"ResizeProperties", []},
        {"RepairCrashProperties", []},
        {"MalformedProperties", []},
        {"LockedProperties", []},
        {"LockedConcurrent", []},
        {"RollbackProperties", []},
        {"InterruptedProperties", []},
        {"TornConcurrent", []},
        {"WriteInterrupted", []}
      ] ++ Enum.map(extra_modules, &{&1, []})

    for {module, replacements} <- sources do
      source = File.read!(Path.join(@fixture, module <> ".lean"))

      source =
        Enum.reduce(replacements, source, fn {old, new}, text ->
          String.replace(text, old, new)
        end)

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), source)
    end

    packages = Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: [
        "io_protocol::locked_append_or_rollback",
        "io_protocol::append_record_or_rollback",
        "io_protocol::locked_append",
        "io_protocol::resize_then_sync",
        "io_protocol::repair_log",
        "io_protocol::append_record",
        "io_protocol::recover_log",
        "io_protocol::recover_record",
        "io_protocol::write_record",
        "io_protocol::write_then_sync",
        "io_protocol::recover_word"
      ],
      execution: :runtime,
      files: :regular,
      tools: tools,
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: Enum.map(sources, fn {name, _} -> "Record." <> name end)
    ]

    {workspace, project, options}
  end
end
