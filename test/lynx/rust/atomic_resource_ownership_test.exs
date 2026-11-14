defmodule Lynx.Rust.AtomicResourceOwnershipTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for owned atomic resource construction")

  @tag :tmp_dir
  test "retains logical cleanup in explicit owned-drop mode without Ordering", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Atomic"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    File.cp!(
      Path.join(@fixture, "OwnedProperties.lean"),
      Path.join(project, "Atomic/OwnedProperties.lean")
    )

    options = [
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      roots: ["atomic_nif::counter_new"],
      lean_project: project,
      module_prefix: "Atomic.Owned",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Atomic.OwnedProperties"],
      required_properties: [
        "Atomic.OwnedProperties.rejected",
        "Atomic.OwnedProperties.registered"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "atomic-nif", options)
    assert [%{status: :ok}] = result.reports

    assert File.read!(Path.join(project, "Atomic/Owned/NativeCodecs.lean")) =~
             "NativeAtomic.dispose"

    refute Enum.any?(result.extraction.audit.external_calls, fn {_, model} ->
             model[:native_atomic_ordering_type]
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "atomic-nif", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    export = Path.join(tmp, "owned-atomic.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
