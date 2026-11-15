defmodule Lynx.Rustler.RuntimeRecordsTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_RECORDS_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do:
      @moduletag(
        skip:
          "set LYNX_NATIVE_RECORDS_DIR to an owned-drops runtime backend with branch duplication"
      )

  @tag :tmp_dir
  test "verifies derived map and struct requests against shared native state", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")
    File.write!(rust, String.replace(File.read!(rust), "LynxAtomicFixture", "LynxRecordFixture"))
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Records"))
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
      root_attribute: "lynx::records",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Records.Extraction",
      only: [atomic_new: 1, atomic_read: 1, atomic_map: 2, atomic_struct: 2]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    facade =
      Enum.reduce(
        [
          {"NEW", "atomic_new"},
          {"READ", "atomic_read"},
          {"MAP", "atomic_map"},
          {"STRUCT", "atomic_struct"}
        ],
        File.read!(Path.join(@fixture, "RecordNifProperties.lean")),
        fn {key, name}, source ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(source, "__#{key}__", binding["lean_name"])
        end
      )

    properties =
      File.read!(Path.join(@fixture, "RecordProperties.lean"))
      |> String.replace("end Records.Properties", facade <> "\nend Records.Properties")

    property = Path.join(project, "Records/Properties.lean")
    File.write!(property, properties)

    options =
      common ++
        [
          proof_modules: ["Records.Properties"],
          required_properties:
            Enum.map(
              ~w(map_field_success map_success struct_field_success struct_success
              contract composed resource_contract matched mismatch updates_agree
              map_field_missing map_missing_first map_missing_second map_nonmap
              struct_missing_tag struct_nonatom_tag struct_wrong_tag
              map_field_error map_second_field_error struct_field_error
              map_expected_error map_replacement_error struct_expected_error
              map_expected_encoded map_replacement_encoded struct_expected_encoded
              facade_new facade_read facade_map facade_struct),
              &("Records.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    # Neither result is custom: the two Decoder-only caches must be discovered.
    for {name, flags} <- [{"atomic_map", 1}, {"atomic_struct", 0}] do
      assert %{
               "arity" => 2,
               "flags" => ^flags,
               "arguments" => [_, %{"decoder_definition_id" => id}]
             } =
               Enum.find(prepared.bindings.bindings, &(&1["name"] == name))

      assert is_integer(id)
    end

    assert Enum.count(prepared.extraction.audit.external_calls, fn {_, model} ->
             Map.has_key?(model, :cache_fields)
           end) == 2

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxRecordFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    native = LynxRecordFixture.Native
    tagged = fn fields -> Map.put(fields, :__struct__, LynxRecordFixture.Request) end

    for name <- [:atomic_map, :atomic_struct] do
      request = fn fields -> if name == :atomic_map, do: fields, else: tagged.(fields) end
      resource = apply(native, :atomic_new, [7])

      assert apply(native, name, [
               resource,
               request.(%{expected: 7, replacement: 11, extra: true})
             ]) == {true, 7}

      assert apply(native, :atomic_read, [resource]) == 11

      assert apply(native, name, [resource, request.(%{expected: 7, replacement: 13})]) ==
               {false, 11}

      for fields <- [%{}, %{expected: 11}, %{replacement: 13}] do
        assert catch_error(apply(native, name, [resource, request.(fields)])) == :badarg
        assert apply(native, :atomic_read, [resource]) == 11
      end

      suffix = if name == :atomic_map, do: "%{}", else: "%StructRequest{}"

      for bad <- [false, -1, 18_446_744_073_709_551_616, "11"] do
        assert catch_error(
                 apply(native, name, [resource, request.(%{expected: bad, replacement: 13})])
               ) ==
                 "Could not decode field :expected on #{suffix}"

        assert catch_error(
                 apply(native, name, [resource, request.(%{expected: 11, replacement: bad})])
               ) ==
                 "Could not decode field :replacement on #{suffix}"

        assert apply(native, :atomic_read, [resource]) == 11
      end
    end

    resource = apply(native, :atomic_new, [7])

    for {tag, reason} <- [{:wrong, :invalid_struct}, {7, :badarg}] do
      assert catch_error(
               apply(native, :atomic_struct, [
                 resource,
                 %{__struct__: tag, expected: false, replacement: false}
               ])
             ) == reason

      assert apply(native, :atomic_read, [resource]) == 7
    end

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/record_laws.ex"))

    for law <-
          ~w(map_matched map_mismatch map_extra map_nonmap map_missing_first map_missing_second
      map_bad_first map_bad_second struct_matched struct_missing_tag struct_nonatom_tag
      struct_wrong_tag struct_bad_first)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "record-laws.export")

    law_options = [
      native: {Lynx.Rustler, options},
      export: export,
      options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
    ]

    reports = Lynx.Laws.verify([beam], law_options)
    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 13
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    assert Enum.all?(
             Lynx.Laws.verify([beam], Keyword.delete(law_options, :export)),
             &(&1.status == :ok and &1.cached)
           )

    [adapter | _] = prepared.external.files
    [%{"source" => adapter_source}] = adapter["preludes"]

    boundary =
      File.read!(Path.join(@fixture, "RecordBoundary.lean"))
      |> String.replace(
        "__NATIVE__",
        :lynx_core_to_leanj.module_name(String.to_atom(prepared.bindings.module))
      )

    boundary_file = Path.join(project, "Records/Boundary.lean")
    boundary_source = adapter_source <> "\n" <> boundary
    File.write!(boundary_file, boundary_source)
    Lynx.Rust.Project.build!(project, ["Records.Boundary"])

    audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Records.Boundary"],
        module: "Records.BoundaryAudit"
      )

    boundary_export = Path.join(tmp, "record-boundary.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [audit], export: boundary_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", boundary_export] ++ sandbox)

    assert status == 0, output

    altered = String.replace(boundary_source, "Lynx.NativeOwnedDrop.drop decoded_arg1;", "")
    assert altered != boundary_source
    File.write!(boundary_file, altered)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.Project.build!(project, ["Records.Boundary"])
      end

    assert Exception.message(error) =~ "proved that the proposition\n  False\nis false"

    File.write!(boundary_file, boundary_source)

    for invalid <- [
          "private axiom uncheckedRecord : False",
          "private theorem unfinishedRecord : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, properties)

    source = Path.join(workspace, "nif/src/records.rs")
    original = File.read!(source)

    for mutation <- [
          String.replace(
            original,
            "request.expected, request.replacement",
            "request.replacement, request.expected"
          ),
          String.replace(original, "LynxRecordFixture.Request", "LynxRecordFixture.Other")
        ] do
      assert mutation != original
      File.write!(source, mutation)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(source, original)
    end
  end
end
