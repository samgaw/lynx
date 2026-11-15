defmodule Lynx.Rustler.ReturnedResultTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RESOURCE_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RESOURCE_DIR for atomic returned errors NIF laws")

  @tag :tmp_dir
  test "verifies resource updates across returned errors and captured panics", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      rust,
      String.replace(File.read!(rust), "LynxAtomicFixture", "LynxReturnedFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Returned"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    common = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      root_attribute: "lynx::returned",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Returned.Extraction",
      only: [atomic_new: 1, atomic_read: 1, atomic_result: 2]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    core_properties =
      File.read!(Path.join(@fixture, "ReturnedProperties.lean"))
      |> String.replace("Atomic.Returned", "Returned.Extraction")
      |> String.replace("Atomic.RustlerBridge", "Returned.RustlerBridge")
      |> String.replace("Returned.ExtractionProperties", "Returned.Properties")

    facade =
      Enum.reduce(
        ~w(NEW READ RESULT),
        File.read!(Path.join(@fixture, "ReturnedNifProperties.lean")),
        fn placeholder, source ->
          binding =
            Enum.find(
              prepared.bindings.bindings,
              &(&1["name"] == "atomic_" <> String.downcase(placeholder))
            )

          String.replace(source, "__#{placeholder}__", binding["lean_name"])
        end
      )

    properties =
      String.replace(
        core_properties,
        "end Returned.Properties",
        facade <> "\nend Returned.Properties"
      )

    property = Path.join(project, "Returned/Properties.lean")
    File.write!(property, properties)

    options =
      common ++
        [
          proof_modules: ["Returned.Properties"],
          required_properties:
            Enum.map(
              ~w(claim_contract badarg_after_update ok_after_update atom_after_update marker_after_update panic_after_update denied_after_update facade_new facade_read facade_result),
              &("Returned.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.map(prepared.bindings.bindings, &{&1["name"], &1["arity"], &1["flags"]})
           |> Enum.sort() == [
             {"atomic_new", 1, 0},
             {"atomic_read", 1, 0},
             {"atomic_result", 2, 1}
           ]

    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    native_source =
      File.read!(Path.join(workspace, "elixir/native.ex"))
      |> String.replace("LynxAtomicFixture", "LynxReturnedFixture")

    Code.compile_string(native_source, Path.join(workspace, "elixir/native.ex"))
    native = LynxReturnedFixture.Native

    for {mode, expected} <- [{0, 7}, {2, :rejected}] do
      resource = apply(native, :atomic_new, [7])
      assert apply(native, :atomic_result, [resource, mode]) == expected
      assert apply(native, :atomic_read, [resource]) == 8
    end

    for {mode, reason} <- [{1, :badarg}, {3, :rust_panicked}, {4, :nif_panicked}, {5, :denied}] do
      resource = apply(native, :atomic_new, [7])
      assert catch_error(apply(native, :atomic_result, [resource, mode])) == reason
      assert apply(native, :atomic_read, [resource]) == 8
    end

    resource = apply(native, :atomic_new, [7])

    for invalid <- [-1, 18_446_744_073_709_551_616, false] do
      assert_raise ArgumentError, fn -> apply(native, :atomic_result, [resource, invalid]) end
      assert apply(native, :atomic_read, [resource]) == 7
    end

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/returned_laws.ex"))

    for law <- ~w(success badarg atom marker panic denied decoder)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "returned-laws.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        export: export,
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      )

    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 7
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    for invalid <- [
          "private axiom uncheckedReturned : False",
          "private theorem unfinishedReturned : False := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Returned.Properties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(property, properties)

    changed =
      String.replace(
        File.read!(rust),
        "0 => Ok(previous)",
        "0 => Ok(0)"
      )

    assert changed != File.read!(rust)
    File.write!(rust, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end
end
