defmodule Lynx.Rustler.RuntimeDecoderTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_DECODER_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do:
      @moduletag(
        skip: "set LYNX_NATIVE_DECODER_DIR to an owned-drops runtime backend for decoder NIF laws"
      )

  @tag :tmp_dir
  test "verifies actual custom decoding with resource cleanup and cross-crate updates", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      rust,
      String.replace(File.read!(rust), "LynxAtomicFixture", "LynxDecodedFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Decoded"))
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
      root_attribute: "lynx::decoded",
      proof_roots: ["atomic_nif::decoding::decode_request"],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Decoded.Extraction",
      only: [atomic_new: 1, atomic_read: 1, atomic_decoded: 3, atomic_decoded_first: 2]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    core_properties = File.read!(Path.join(@fixture, "DecoderProperties.lean"))

    facade =
      Enum.reduce(
        [
          {"NEW", "atomic_new"},
          {"READ", "atomic_read"},
          {"DECODED", "atomic_decoded"},
          {"FIRST", "atomic_decoded_first"}
        ],
        File.read!(Path.join(@fixture, "DecoderNifProperties.lean")),
        fn {placeholder, name}, source ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(source, "__#{placeholder}__", binding["lean_name"])
        end
      )

    properties =
      String.replace(
        core_properties,
        "end Decoded.Properties",
        facade <> "\nend Decoded.Properties"
      )

    property = Path.join(project, "Decoded/Properties.lean")
    File.write!(property, properties)

    options =
      common ++
        [
          proof_modules: ["Decoded.Properties"],
          required_properties:
            Enum.map(
              ~w(generic_decoder decoder_error decoder_range decoder_zero decoder_one decoder_panic decoder_marker decoder_atom decoder_badarg claim_contract current_contract two_contract disabled_contract enabled_updates disabled_preserves facade_new facade_read facade_decoded facade_first),
              &("Decoded.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.map(prepared.bindings.bindings, &{&1["name"], &1["arity"], &1["flags"]})
           |> Enum.sort() == [
             {"atomic_decoded", 3, 1},
             {"atomic_decoded_first", 2, 0},
             {"atomic_new", 1, 0},
             {"atomic_read", 1, 0}
           ]

    assert Enum.any?(
             prepared.verification.unverified_external_calls,
             &(&1.lean == "Lynx.Rustler.NativeDecoding.u64" and
                 &1.implementation_verified == false)
           )

    decoded = Enum.find(prepared.bindings.bindings, &(&1["name"] == "atomic_decoded"))
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
      |> String.replace("LynxAtomicFixture", "LynxDecodedFixture")

    Code.compile_string(native_source, Path.join(workspace, "elixir/native.ex"))
    native = LynxDecodedFixture.Native

    for {request, enabled, expected, final} <- [
          {0, true, 7, 7},
          {1, true, 7, 9},
          {1, false, 7, 7},
          {4, true, :decoder_rejected, 7}
        ] do
      resource = apply(native, :atomic_new, [7])
      assert apply(native, :atomic_decoded, [resource, request, enabled]) == expected
      assert apply(native, :atomic_read, [resource]) == final
    end

    for {request, reason} <- [
          {-1, :badarg},
          {2, :nif_panicked},
          {3, :rust_panicked},
          {5, :badarg}
        ] do
      resource = apply(native, :atomic_new, [7])
      assert catch_error(apply(native, :atomic_decoded, [resource, request, true])) == reason
      assert apply(native, :atomic_read, [resource]) == 7
    end

    resource = apply(native, :atomic_new, [7])

    for invalid <- [-1, 18_446_744_073_709_551_616, false] do
      assert_raise ArgumentError, fn ->
        apply(native, :atomic_decoded, [resource, invalid, true])
      end

      assert apply(native, :atomic_read, [resource]) == 7
    end

    assert_raise ArgumentError, fn -> apply(native, :atomic_decoded, [resource, 1, :invalid]) end
    assert apply(native, :atomic_read, [resource]) == 7
    assert apply(native, :atomic_decoded_first, [4, :invalid]) == :decoder_rejected

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/decoded_laws.ex"))

    for law <-
          ~w(updated read_only disabled range panic marker atom badarg later_failure first_failure_wins wraparound)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "decoded-laws.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        export: export,
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      )

    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 11
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    # Re-elaborate the exact generated adapter source with full heap properties.
    # This catches ownership leaks that successful later read calls cannot detect.
    [adapter | _] = prepared.external.files
    [%{"source" => adapter_source}] = adapter["preludes"]

    boundary =
      File.read!(Path.join(@fixture, "DecoderBoundary.lean"))
      |> String.replace(
        "__NATIVE__",
        :lynx_core_to_leanj.module_name(String.to_atom(prepared.bindings.module))
      )

    boundary_source = adapter_source <> "\n" <> boundary
    boundary_file = Path.join(project, "Decoded/Boundary.lean")
    File.write!(boundary_file, boundary_source)
    Lynx.Rust.Project.build!(project, ["Decoded.Boundary"])

    boundary_audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Decoded.Boundary"],
        module: "Decoded.BoundaryAudit"
      )

    boundary_export = Path.join(tmp, "decoder-boundary.export")

    assert [%{status: :ok}] =
             Lynx.Commands.verify!(project, [boundary_audit], export: boundary_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", boundary_export] ++ sandbox)

    assert status == 0, output

    leaking = String.replace(boundary_source, "Lynx.NativeOwnedDrop.drop decoded_arg1; ", "")
    assert leaking != boundary_source
    File.write!(boundary_file, leaking)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Decoded.Boundary"])
    end

    File.write!(boundary_file, boundary_source)

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    for invalid <- [
          "private axiom uncheckedDecoded : False",
          "private theorem unfinishedDecoded : False := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Decoded.Properties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(property, properties)

    core = Path.join(workspace, "core/src/lib.rs")

    changed =
      String.replace(
        File.read!(core),
        "counter.fetch_add(1,",
        "counter.fetch_add(2,"
      )

    assert changed != File.read!(core)
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    # Changing the actual Decoder invalidates its implementation-linked proof.
    File.write!(core, String.replace(changed, "counter.fetch_add(2,", "counter.fetch_add(1,"))
    decoder_source = Path.join(workspace, "nif/src/decoding.rs")
    original = File.read!(decoder_source)
    altered = String.replace(original, "RaiseAtom(\"rust_panicked\")", "RaiseAtom(\"changed\")")
    assert altered != original
    File.write!(decoder_source, altered)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end
end
