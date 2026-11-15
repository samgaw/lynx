defmodule Lynx.Rustler.RuntimeEncoderTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_ENCODER_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do:
      @moduletag(
        skip:
          "set LYNX_NATIVE_ENCODER_DIR to an owned-drops runtime backend with branch duplication"
      )

  @tag :tmp_dir
  test "verifies actual return encoders after native updates and conditional cleanup", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      rust,
      String.replace(File.read!(rust), "LynxAtomicFixture", "LynxEncodedNativeFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Encoded"))
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
      root_attribute: "lynx::encoded",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Encoded.Extraction",
      only: [
        atomic_new: 1,
        atomic_read: 1,
        atomic_reply: 3,
        atomic_reply_option: 3,
        atomic_reply_result: 3,
        atomic_reply_tuple: 3,
        atomic_reply_checked: 3,
        atomic_reply_nif_result: 3
      ]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    facade =
      Enum.reduce(
        [
          {"NEW", "atomic_new"},
          {"READ", "atomic_read"},
          {"REPLY", "atomic_reply"},
          {"OPTION", "atomic_reply_option"},
          {"RESULT", "atomic_reply_result"},
          {"TUPLE", "atomic_reply_tuple"},
          {"CHECKED", "atomic_reply_checked"},
          {"RETURNED", "atomic_reply_nif_result"}
        ],
        File.read!(Path.join(@fixture, "EncoderNifProperties.lean")),
        fn {key, name}, source ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(source, "__#{key}__", binding["lean_name"])
        end
      )

    [resource_type] = prepared.resource_registration.types
    facade = String.replace(facade, "__RESOURCE_TYPE__", JSON.encode!(resource_type.tag))

    properties =
      File.read!(Path.join(@fixture, "EncoderProperties.lean"))
      |> String.replace("end Encoded.Properties", facade <> "\nend Encoded.Properties")

    property = Path.join(project, "Encoded/Properties.lean")
    File.write!(property, properties)

    options =
      common ++
        [
          proof_modules: ["Encoded.Properties"],
          required_properties:
            Enum.map(
              ~w(encoder_spec checked_encoder checked_panics checked_spec
        contract composed matched mismatch facade_new facade_read facade_reply facade_optional
        facade_result facade_tuple facade_checked facade_returned returned_error_cleanup),
              &("Encoded.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    reply = Enum.find(prepared.bindings.bindings, &(&1["name"] == "atomic_reply"))

    assert %{
             "flags" => 1,
             "arity" => 3,
             "result" => %{
               "encoder_monad" => "Lynx.NativeM",
               "encoder_definition_id" => encoder_id,
               "lean" => lean
             }
           } = reply

    type_id =
      Enum.find(prepared.extraction.translation["types"], &(&1["lean_name"] == lean))["def_id"]

    for functions <- [
          Enum.reject(prepared.extraction.audit.functions, &(&1["def_id"] == encoder_id)),
          Enum.map(prepared.extraction.audit.functions, fn f ->
            if f["def_id"] == encoder_id, do: Map.put(f, "body", "Opaque"), else: f
          end)
        ] do
      audit = %{prepared.extraction.audit | functions: functions}

      assert_raise ArgumentError,
                   ~r/missing, opaque or mismatched first-party Rustler Encoder/,
                   fn ->
                     Lynx.Rustler.EncoderModels.binding!(
                       type_id,
                       audit,
                       prepared.extraction.translation
                     )
                   end
    end

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxEncodedNativeFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    native = LynxEncodedNativeFixture.Native

    for {name, expected, replacement, result, current} <- [
          {:atomic_reply, 7, 11, {7, 11}, 11},
          {:atomic_reply, 8, 11, {7, 7}, 7},
          {:atomic_reply_option, 7, 0, nil, 0},
          {:atomic_reply_option, 7, 11, 11, 11},
          {:atomic_reply_result, 7, 11, {:ok, {7, 11}}, 11},
          {:atomic_reply_result, 8, 11, {:error, 7}, 7},
          {:atomic_reply_tuple, 7, 11, {{7, 11}, 11}, 11},
          {:atomic_reply_checked, 7, 11, 11, 11},
          {:atomic_reply_nif_result, 7, 11, {7, 11}, 11}
        ] do
      resource = apply(native, :atomic_new, [7])
      assert apply(native, name, [resource, expected, replacement]) == result
      assert apply(native, :atomic_read, [resource]) == current
    end

    resource = apply(native, :atomic_new, [7])
    assert catch_error(apply(native, :atomic_reply_checked, [resource, 7, 0])) == :nif_panicked
    assert apply(native, :atomic_read, [resource]) == 0

    assert catch_error(
             apply(native, :atomic_reply_nif_result, [resource, 18_446_744_073_709_551_615, 11])
           ) == :rust_panicked

    assert apply(native, :atomic_read, [resource]) == 0

    for invalid <- [-1, 18_446_744_073_709_551_616] do
      assert catch_error(apply(native, :atomic_reply, [resource, invalid, 11])) == :badarg
      assert apply(native, :atomic_read, [resource]) == 0
    end

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/encoded_laws.ex"))

    for law <- ~w(ordered_reply mismatched_reply absent_reply present_reply ok_reply error_reply
      tuple_reply checked_reply encoder_panic returned_ok returned_error)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "encoder-laws.export")

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

    [adapter | _] = prepared.external.files
    [%{"source" => adapter_source}] = adapter["preludes"]

    boundary =
      File.read!(Path.join(@fixture, "EncoderBoundary.lean"))
      |> String.replace(
        "__NATIVE__",
        :lynx_core_to_leanj.module_name(String.to_atom(prepared.bindings.module))
      )

    boundary_file = Path.join(project, "Encoded/Boundary.lean")
    boundary_source = adapter_source <> "\n" <> boundary
    File.write!(boundary_file, boundary_source)
    Lynx.Rust.Project.build!(project, ["Encoded.Boundary"])

    audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Encoded.Boundary"],
        module: "Encoded.BoundaryAudit"
      )

    boundary_export = Path.join(tmp, "encoder-boundary.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [audit], export: boundary_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", boundary_export] ++ sandbox)

    assert status == 0, output

    altered =
      boundary_source
      |> String.replace("Lynx.Rustler.executeNative", "Encoded.Unprotected.execute")
      |> String.replace("Rustler.executeNative", "Encoded.Unprotected.execute")
      |> String.replace(
        "public section",
        """
        public section
        namespace Encoded.Unprotected
        @[expose] def execute {α : Type} (computation : Lynx.Result α)
            (encode : α → Lynx.Term) : Lynx.Result Lynx.Term := do
          let value ← computation
          Lynx.Result.ok (encode value)
        end Encoded.Unprotected
        """,
        global: false
      )

    assert altered != boundary_source
    File.write!(boundary_file, altered)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.Project.build!(project, ["Encoded.Boundary"])
      end

    assert Exception.message(error) =~ "unsolved goals"

    File.write!(boundary_file, boundary_source)

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    for invalid <- [
          "private axiom uncheckedEncoder : False",
          "private theorem unfinishedEncoder : False := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Encoded.Properties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(property, properties)
    encoding = Path.join(workspace, "nif/src/encoding.rs")
    original = File.read!(encoding)

    reversed =
      String.replace(
        original,
        "    previous: u64,\n    current: u64,",
        "    current: u64,\n    previous: u64,"
      )

    assert reversed != original
    File.write!(encoding, reversed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(encoding, original)

    no_panic =
      String.replace(original, "assert!(self.value != 0,", "assert!(self.value == self.value,")

    assert no_panic != original
    File.write!(encoding, no_panic)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end
end
