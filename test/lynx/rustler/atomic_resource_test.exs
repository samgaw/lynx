defmodule Lynx.Rustler.AtomicResourceTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RESOURCE_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RESOURCE_DIR for resource atomic NIF proofs")

  @tag :tmp_dir
  test "verifies shared atomic NIFs, panic cleanup and ordinary concurrent laws", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Atomic"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))

    File.cp!(
      Path.join(@fixture, "ResourceProperties.lean"),
      Path.join(project, "Atomic/ResourceProperties.lean")
    )

    common = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      root_attribute: "lynx::atomic",
      proof_roots: ["atomic_nif::counter_cycle"],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Atomic.Resource",
      only: [atomic_new: 1, atomic_claim: 1, atomic_pair: 1, atomic_read: 1, atomic_checked: 2]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    properties =
      Enum.reduce(
        ~w(NEW CLAIM PAIR READ CHECKED),
        File.read!(Path.join(@fixture, "NifProperties.lean")),
        fn placeholder, source ->
          name = "atomic_" <> String.downcase(placeholder)
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(source, "__#{placeholder}__", binding["lean_name"])
        end
      )

    File.write!(Path.join(project, "Atomic/NifProperties.lean"), properties)

    options =
      common ++
        [
          proof_modules: ["Atomic.ResourceProperties", "Atomic.NifProperties"],
          required_properties:
            Enum.map(
              ~w(claim_contract pair_contract cycle cycle_foreign unregistered accepted rejected facade_new facade_claim facade_pair facade_read facade_checked),
              &("Atomic.ResourceProperties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.map(prepared.bindings.bindings, &{&1["name"], &1["arity"], &1["flags"]})
           |> Enum.sort() == [
             {"atomic_checked", 2, 1},
             {"atomic_claim", 1, 1},
             {"atomic_new", 1, 0},
             {"atomic_pair", 1, 1},
             {"atomic_read", 1, 0}
           ]

    assert %{status: :validated_configuration, types: [%{rust_name: "atomic_nif::Counter"}]} =
             prepared.resource_registration

    assert Enum.any?(
             prepared.verification.unverified_external_calls,
             &String.contains?(&1.label, "AtomicU64")
           )

    assert File.read!(Path.join(project, "Atomic/Resource/NativeCodecs.lean")) =~
             "NativeAtomic.dispose"

    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "atomic-resource.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))
    Code.compile_file(Path.join(workspace, "elixir/native.ex"))
    native = LynxAtomicFixture.Native
    resource = apply(native, :atomic_new, [7])
    assert apply(native, :atomic_pair, [resource]) == {7, 8}
    assert apply(native, :atomic_claim, [resource]) == 9
    assert apply(native, :atomic_read, [resource]) == 10
    maximum = 18_446_744_073_709_551_615
    resource = apply(native, :atomic_new, [maximum])
    assert apply(native, :atomic_pair, [resource]) == {maximum, 0}
    assert apply(native, :atomic_read, [resource]) == 1

    for invalid <- [-1, maximum + 1, false],
        do: assert_raise(ArgumentError, fn -> apply(native, :atomic_new, [invalid]) end)

    assert_raise ArgumentError, fn -> apply(native, :atomic_claim, [7]) end
    assert catch_error(apply(native, :atomic_checked, [7, false])) == :nif_panicked

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/laws.ex"))

    for law <-
          ~w(shared_sequence wraparound accepted_request rejected_request invalid_resource integer_boundaries competing_tickets)a,
        do: assert(apply(law_module, law, []))

    law_export = Path.join(tmp, "atomic-laws.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        export: law_export,
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      )

    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 7

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", law_export] ++ sandbox)

    assert status == 0, output

    [{_, false_beam}] = Code.compile_file(Path.join(workspace, "elixir/false_laws.ex"))

    false_reports =
      Lynx.Laws.verify([false_beam],
        native: {Lynx.Rustler, options},
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      )

    assert Enum.any?(false_reports, fn report ->
             report.status == :error &&
               Enum.any?(report.diagnostics, fn diagnostic ->
                 diagnostic.declaration == "wrong_readback/0" &&
                   (String.contains?(diagnostic.message, "Expectation") or
                      String.contains?(diagnostic.message, "postcondition"))
               end)
           end)

    codec = Path.join(project, "Atomic/Resource/NativeCodecs.lean")
    source = File.read!(codec)

    for invalid <- [
          "private axiom uncheckedAtomic : False",
          "private theorem unfinishedAtomic : False := by sorry"
        ] do
      File.write!(codec, source <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Atomic.Resource.NativeCodecs"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(codec, source)

    for {root, message} <- [
          {"unsupported_owner_tuple", ~r/scalar\/unit tuples/},
          {"unsupported_discard", ~r/native owner lifetime/}
        ] do
      assert_raise CompileError, message, fn ->
        Lynx.Rust.verify!(workspace, "atomic-nif",
          tools: @tools,
          execution: :runtime,
          unwind: :captured,
          roots: ["atomic_nif::" <> root],
          lean_project: project,
          module_prefix: "Atomic.Resource",
          build_dir: Path.join(tmp, "build")
        )
      end
    end

    core = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(core)
    File.write!(core, String.replace(rust, "counter.fetch_add(1,", "counter.fetch_add(2,"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, rust)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
