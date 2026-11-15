defmodule Lynx.Rustler.RuntimeScalarsTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_SCALARS_DIR")
  @scalars ~w(bool i8 i16 i32 i64 u8 u16 u32 u64)
  @moduletag timeout: 1_800_000
  unless @tools,
    do:
      @moduletag(
        skip: "set LYNX_NATIVE_SCALARS_DIR for compiled scalar Decoder and native-state proofs"
      )

  @tag :tmp_dir
  test "verifies scalar dictionaries, SDK narrowing and native update control", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")
    File.write!(rust, String.replace(File.read!(rust), "LynxAtomicFixture", "LynxScalarFixture"))
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Scalars"))
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
      root_attribute: "lynx::scalars",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Scalars.Extraction",
      only:
        [atomic_new: 1, atomic_read: 1, atomic_scalar: 2] ++
          Enum.map(@scalars, &{String.to_atom("scalar_" <> &1), 1})
    ]

    prepared = Lynx.Rustler.prepare!(common)

    names =
      [{"NEW", "atomic_new"}, {"READ", "atomic_read"}, {"MIXED", "atomic_scalar"}] ++
        Enum.map(@scalars, &{String.upcase(&1), "scalar_" <> &1})

    facade =
      Enum.reduce(names, File.read!(Path.join(@fixture, "ScalarNifProperties.lean")), fn {key,
                                                                                          name},
                                                                                         source ->
        binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
        String.replace(source, "__#{key}__", binding["lean_name"])
      end)

    properties =
      File.read!(Path.join(@fixture, "ScalarProperties.lean"))
      |> String.replace("end Scalars.Properties", facade <> "\nend Scalars.Properties")

    property = Path.join(project, "Scalars/Properties.lean")
    File.write!(property, properties)

    roots =
      Enum.map(@scalars, &(&1 <> "_decoded")) ++
        Enum.map(~w(i8 i16 u8 u16), &(&1 <> "_narrows")) ++
        ~w(request_decoded contract composed current_contract updated disabled negative signed_field_error request_signed_error request_signed_encoded facade_new facade_read facade_mixed) ++
        Enum.map(@scalars, &("facade_" <> &1))

    options =
      common ++
        [
          proof_modules: ["Scalars.Properties"],
          required_properties: Enum.map(roots, &("Scalars.Properties." <> &1))
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    for scalar <- @scalars do
      assert Enum.any?(prepared.extraction.audit.external_calls, fn {_, model} ->
               model.lean == "Lynx.Rustler.NativeDecoding.#{scalar}"
             end)
    end

    assert Enum.any?(
             prepared.verification.external_models,
             &String.contains?(&1, "lossless u16-to-u64")
           )

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxScalarFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    native = LynxScalarFixture.Native

    for {name, cases} <- [
          {:scalar_bool, [{true, true}, {false, false}]},
          {:scalar_i8, [{255, -1}, {-2_147_483_648, 0}, {2_147_483_647, -1}]},
          {:scalar_i16, [{65535, -1}, {-2_147_483_648, 0}, {2_147_483_647, -1}]},
          {:scalar_i32, [{-2_147_483_648, -2_147_483_648}, {2_147_483_647, 2_147_483_647}]},
          {:scalar_i64,
           [
             {-9_223_372_036_854_775_808, -9_223_372_036_854_775_808},
             {9_223_372_036_854_775_807, 9_223_372_036_854_775_807}
           ]},
          {:scalar_u8, [{256, 0}, {4_294_967_295, 255}]},
          {:scalar_u16, [{65537, 1}, {4_294_967_295, 65535}]},
          {:scalar_u32, [{0, 0}, {4_294_967_295, 4_294_967_295}]},
          {:scalar_u64, [{0, 0}, {18_446_744_073_709_551_615, 18_446_744_073_709_551_615}]}
        ] do
      for {input, expected} <- cases, do: assert(apply(native, name, [{input}]) == expected)
    end

    for {name, bad_values, record} <- [
          {:scalar_bool, [0, 1, nil], "BoolValue"},
          {:scalar_i8, [-2_147_483_649, 2_147_483_648, true], "I8Value"},
          {:scalar_i16, [-2_147_483_649, 2_147_483_648, true], "I16Value"},
          {:scalar_i32, [-2_147_483_649, 2_147_483_648, true], "I32Value"},
          {:scalar_i64, [-9_223_372_036_854_775_809, 9_223_372_036_854_775_808, true],
           "I64Value"},
          {:scalar_u8, [-1, 4_294_967_296, true], "U8Value"},
          {:scalar_u16, [-1, 4_294_967_296, true], "U16Value"},
          {:scalar_u32, [-1, 4_294_967_296, true], "U32Value"},
          {:scalar_u64, [-1, 18_446_744_073_709_551_616, true], "U64Value"}
        ] do
      for value <- bad_values,
          do:
            assert(
              catch_error(apply(native, name, [{value}])) ==
                "Could not decode field value on #{record}"
            )
    end

    for {initial, request, result, current} <- [
          {0, {true, 5, 65537}, {5, 1, true, 0}, 1},
          {0, {true, 255, 65537}, {-1, 1, false, 0}, 0},
          {0, {false, 5, 65537}, {5, 1, false, 0}, 0},
          {7, {true, 5, 11}, {5, 11, false, 7}, 7}
        ] do
      resource = apply(native, :atomic_new, [initial])
      assert apply(native, :atomic_scalar, [resource, request]) == result
      assert apply(native, :atomic_read, [resource]) == current
    end

    resource = apply(native, :atomic_new, [7])

    for {request, field} <- [
          {{1, 5, 11}, "enabled"},
          {{true, 2_147_483_648, 11}, "signed"},
          {{true, 5, -1}, "unsigned"}
        ] do
      assert catch_error(apply(native, :atomic_scalar, [resource, request])) ==
               "Could not decode field #{field} on Request"

      assert apply(native, :atomic_read, [resource]) == 7
    end

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/scalar_laws.ex"))

    laws =
      Enum.map(@scalars, &String.to_atom("echo_" <> &1)) ++
        ~w(mixed_update mixed_negative mixed_disabled mixed_mismatch mixed_bad_signed)a

    for law <- laws, do: assert(apply(law_module, law, []))
    export = Path.join(tmp, "scalar-laws.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        export: export,
        options: [maxRecDepth: 8192, maxHeartbeats: 16_000_000]
      )

    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 14
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    [adapter | _] = prepared.external.files
    [%{"source" => adapter_source}] = adapter["preludes"]

    boundary =
      File.read!(Path.join(@fixture, "ScalarBoundary.lean"))
      |> String.replace(
        "__NATIVE__",
        :lynx_core_to_leanj.module_name(String.to_atom(prepared.bindings.module))
      )

    boundary_file = Path.join(project, "Scalars/Boundary.lean")
    File.write!(boundary_file, adapter_source <> "\n" <> boundary)
    Lynx.Rust.Project.build!(project, ["Scalars.Boundary"])

    audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Scalars.Boundary"],
        module: "Scalars.BoundaryAudit"
      )

    boundary_export = Path.join(tmp, "scalar-boundary.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [audit], export: boundary_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", boundary_export] ++ sandbox)

    assert status == 0, output

    # A narrower SDK input range contradicts the actual derived decoding proof.
    bridge = Path.join(project, "Scalars/RustlerBridge.lean")
    original_bridge = File.read!(bridge)

    changed =
      String.replace(original_bridge, "decodeSigned .I8 32 term", "decodeSigned .I8 8 term")

    assert changed != original_bridge
    File.write!(bridge, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Scalars.Properties"])
    end

    File.write!(bridge, original_bridge)

    for invalid <- [
          "private axiom uncheckedScalar : False",
          "private theorem unfinishedScalar : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, properties)
    source = Path.join(workspace, "nif/src/scalars.rs")
    original = File.read!(source)
    changed = String.replace(original, "request.signed >= 0", "request.signed <= 0")
    assert changed != original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end
end
