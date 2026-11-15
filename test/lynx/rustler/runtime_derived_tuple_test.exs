defmodule Lynx.Rustler.RuntimeDerivedTupleTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_DERIVED_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do:
      @moduletag(
        skip:
          "set LYNX_NATIVE_DERIVED_DIR to an owned-drops runtime backend with branch duplication"
      )

  @tag :tmp_dir
  test "verifies generated tuple decoding and conditional native resource updates", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      rust,
      String.replace(File.read!(rust), "LynxAtomicFixture", "LynxDerivedNativeFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Derived"))
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
      owned_drops: true,
      branching: :duplicate,
      root_attribute: "lynx::tuple_decode",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Derived.Extraction",
      only: [atomic_new: 1, atomic_read: 1, atomic_tuple: 2]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    core_properties = File.read!(Path.join(@fixture, "DerivedDecoderProperties.lean"))

    facade =
      Enum.reduce(
        [
          {"NEW", "atomic_new"},
          {"READ", "atomic_read"},
          {"TUPLE", "atomic_tuple"}
        ],
        File.read!(Path.join(@fixture, "DerivedDecoderNifProperties.lean")),
        fn {placeholder, name}, source ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(source, "__#{placeholder}__", binding["lean_name"])
        end
      )

    properties =
      String.replace(
        core_properties,
        "end Derived.Properties",
        facade <> "\nend Derived.Properties"
      )

    property = Path.join(project, "Derived/Properties.lean")
    File.write!(property, properties)

    options =
      common ++
        [
          proof_modules: ["Derived.Properties"],
          required_properties:
            Enum.map(
              ~w(field_success decoder_success non_tuple arity_rejected oversized field_expected_error field_replacement_error decoder_expected_error decoder_replacement_error contract composed resource_contract matched mismatch facade_new facade_read facade_tuple),
              &("Derived.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.map(prepared.bindings.bindings, &{&1["name"], &1["arity"], &1["flags"]})
           |> Enum.sort() == [
             {"atomic_new", 1, 0},
             {"atomic_read", 1, 0},
             {"atomic_tuple", 2, 1}
           ]

    assert Enum.any?(
             prepared.verification.unverified_external_calls,
             &(&1.lean == "Lynx.Rustler.NativeDecoding.u64" and
                 &1.implementation_verified == false)
           )

    decoded = Enum.find(prepared.bindings.bindings, &(&1["name"] == "atomic_tuple"))
    decoder_id = Enum.at(decoded["arguments"], 1)["decoder_definition_id"]

    missing = %{
      prepared.extraction.audit
      | functions: Enum.reject(prepared.extraction.audit.functions, &(&1["def_id"] == decoder_id))
    }

    assert_raise ArgumentError,
                 ~r/missing, opaque or mismatched first-party Rustler Decoder/,
                 fn ->
                   Lynx.Rustler.Bindings.link!(
                     prepared.bindings,
                     missing,
                     prepared.extraction.translation,
                     resource_types: prepared.resource_registration.types,
                     result_monad: "Lynx.NativeM"
                   )
                 end

    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    native_source =
      File.read!(Path.join(workspace, "elixir/native.ex"))
      |> String.replace("LynxAtomicFixture", "LynxDerivedNativeFixture")

    Code.compile_string(native_source, Path.join(workspace, "elixir/native.ex"))
    native = LynxDerivedNativeFixture.Native

    resource = apply(native, :atomic_new, [7])
    assert apply(native, :atomic_tuple, [resource, {7, 11}]) == {true, 7}
    assert apply(native, :atomic_tuple, [resource, {7, 99}]) == {false, 11}
    assert apply(native, :atomic_read, [resource]) == 11

    for {invalid, reason} <- [
          {false, :badarg},
          {{false}, :badarg},
          {{7, 11, 13}, :badarg},
          {{false, 11}, "Could not decode field expected on Request"},
          {{11, -1}, "Could not decode field replacement on Request"},
          {{false, :invalid}, "Could not decode field expected on Request"}
        ] do
      assert catch_error(apply(native, :atomic_tuple, [resource, invalid])) == reason
      assert apply(native, :atomic_read, [resource]) == 11
    end

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/derived_laws.ex"))

    for law <-
          ~w(matched mismatch not_tuple short_tuple long_tuple expected_error replacement_error first_error_wins maximum)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "derived-laws.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        export: export,
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      )

    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 9
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    # Re-elaborate the exact generated adapter source with full heap properties.
    # This catches ownership leaks that successful later read calls cannot detect.
    [adapter | _] = prepared.external.files
    [%{"source" => adapter_source}] = adapter["preludes"]

    boundary =
      File.read!(Path.join(@fixture, "DerivedDecoderBoundary.lean"))
      |> String.replace(
        "__NATIVE__",
        :lynx_core_to_leanj.module_name(String.to_atom(prepared.bindings.module))
      )

    boundary_source = adapter_source <> "\n" <> boundary
    boundary_file = Path.join(project, "Derived/Boundary.lean")
    File.write!(boundary_file, boundary_source)
    Lynx.Rust.Project.build!(project, ["Derived.Boundary"])

    boundary_audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Derived.Boundary"],
        module: "Derived.BoundaryAudit"
      )

    boundary_export = Path.join(tmp, "derived-boundary.export")

    assert [%{status: :ok}] =
             Lynx.Commands.verify!(project, [boundary_audit], export: boundary_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", boundary_export] ++ sandbox)

    assert status == 0, output

    leaking = String.replace(boundary_source, "Lynx.NativeOwnedDrop.drop decoded_arg1; ", "")
    assert leaking != boundary_source
    File.write!(boundary_file, leaking)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Derived.Boundary"])
    end

    File.write!(boundary_file, boundary_source)

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    for invalid <- [
          "private axiom uncheckedDerived : False",
          "private theorem unfinishedDerived : False := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Derived.Properties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(property, properties)

    core = Path.join(workspace, "analysis/src/lib.rs")
    original_core = File.read!(core)

    changed =
      String.replace(
        original_core,
        "Ok(previous) => (true, previous)",
        "Ok(previous) => (false, previous)"
      )

    assert changed != original_core
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, original_core)

    decoder_source = Path.join(workspace, "nif/src/derived.rs")
    original = File.read!(decoder_source)

    altered =
      String.replace(
        original,
        "    expected: u64,\n    replacement: u64,",
        "    replacement: u64,\n    expected: u64,"
      )

    assert altered != original
    File.write!(decoder_source, altered)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end
end
