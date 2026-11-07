defmodule Lynx.Rust.IoFixture do
  @moduledoc false
  @fixture Path.expand("../fixtures/rust_io", __DIR__)

  def prepare!(tmp, tools, extra_modules \\ []) do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol),
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
