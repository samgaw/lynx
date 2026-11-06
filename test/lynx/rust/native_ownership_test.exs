defmodule Lynx.Rust.NativeOwnershipTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "lynx-result-monad-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned result-monad backend")

  @tag :tmp_dir
  test "transfers ownership into an actual cross-crate callee and retains its failure effects", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))

    File.cp!(
      Path.join(@fixture, "NativeOwnership.lean"),
      Path.join(project, "Runtime/OwnershipProperties.lean")
    )

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::mutex_release_checked"],
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Ownership",
      proof_modules: ["Runtime.OwnershipProperties"],
      required_properties:
        Enum.map(
          ~w(release_contract release_state composed_release),
          &("Runtime.OwnershipProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Runtime.OwnershipProperties.composed_release" &&
               "Runtime.OwnershipProperties.release_contract" in row.contracts_used
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.OwnershipProperties"])
    export = Path.join(tmp, "ownership.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    # Acquiring a guard does not admit opaque unwrap or guard operations.
    assert_raise CompileError, ~r/unverified external Rust call core::result/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "effects-native",
        Keyword.put(options, :roots, ["effects_native::mutex_guarded_increment"])
      )
    end

    # Callee admission is checked independently; transferring ownership cannot
    # hide a panic that would require currently unsupported unwind destruction.
    core = Path.join(workspace, "core/src/lib.rs")
    source = File.read!(core)

    reordered =
      String.replace(
        source,
        "drop(mutex);\n    assert!(accepted);",
        "assert!(accepted);\n    drop(mutex);"
      )

    refute source == reordered
    File.write!(core, reordered)

    assert_raise CompileError, ~r/native owner lifetime|structural drop erasure rejected/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(core, source)

    # An actual implementation change cannot reuse the previous composed proof.
    native = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(native)

    changed =
      String.replace(
        source,
        "effects_core::release_checked(Mutex::new(value), accepted);",
        "effects_core::release_checked(Mutex::new(value), true);"
      )

    refute source == changed
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end
end
