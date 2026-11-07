defmodule Lynx.Rustler.FileResourceTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
           String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "+owned-drops-v1"),
         do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-drops backend")

  @tag :tmp_dir
  test "a compiled release-only resource NIF retains the VM-owned file", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "FileResource"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    base = [
      workspace: workspace,
      package: "effects-native",
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "FileResource.Extraction",
      cargo: [features: ["file-resource-handles"]],
      only: [file_release: 1],
      execution: :runtime,
      files: :regular,
      owned_drops: true
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert %{
             status: :validated_configuration,
             types: [%{rust_name: "effects_native::FileResource"}]
           } = prepared.resource_registration

    assert [%{"name" => "file_release", "flags" => 2, "lean_name" => function}] =
             prepared.bindings.bindings

    assert [%{lean_name: "effects_native.FileResource.drop_owned"}] =
             prepared.verification.resource_cleanup

    model = Path.join(project, "FileResource/Model.lean")
    File.cp!(Path.join(@fixture, "NativeFileResourceModel.lean"), model)

    source =
      File.read!(Path.join(@fixture, "NativeFileResourceNif.lean"))
      |> String.replace("__RELEASE__", function)

    property = Path.join(project, "FileResource/NifProperties.lean")
    File.write!(property, source)

    options =
      base ++
        [
          proof_modules: ["FileResource.Model", "FileResource.NifProperties"],
          required_properties: [
            "FileResource.Properties.cleanup_contract",
            "FileResource.Properties.cleanup_ready",
            "FileResource.NifProperties.release_call",
            "FileResource.NifProperties.release_preserves_file"
          ]
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    assert checked.verification.files == :regular
    assert Enum.any?(checked.verification.guarantees, &(&1.kind == :nif_adapter))

    load_native(prepared.library, tmp)

    for invalid <- [0, false, make_ref()],
        do:
          assert_raise(ArgumentError, fn ->
            apply(LynxFileResourceFixture.Native, :file_release, [invalid])
          end)

    path = Path.join(tmp, "laws.ex")
    File.cp!(Path.join(@fixture, "file_resource_laws.ex"), path)
    [{_, beam}] = Code.compile_file(path)
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

    assert Enum.any?(
             Enum.flat_map(reports, &Map.get(&1, :guarantees, [])),
             &(&1.kind == :elixir_law)
           )

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
             &(&1.status == :ok and &1.cached)
           )

    export = Path.join(tmp, "file-nif.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom fileNifTrust : False",
          "private theorem unfinishedFileNif : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(property, source)
    end

    native = Path.join(workspace, "native/src/lib.rs")
    rust = File.read!(native)

    changed =
      String.replace(
        rust,
        "pub fn file_resource_nif_release(resource: rustler::ResourceArc<FileResource>) {\n    file_resource_release(resource);\n}",
        "pub fn file_resource_nif_release(resource: rustler::ResourceArc<FileResource>) {\n    file_resource_release(resource);\n    panic!();\n}"
      )

    refute changed == rust
    File.write!(native, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert error.message =~ "FileResource/NifProperties.lean:"
    File.write!(native, rust)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    assert_raise CompileError, fn -> Lynx.Rustler.prepare!(Keyword.delete(options, :files)) end
  end

  defp load_native(artifact, tmp) do
    :code.purge(LynxFileResourceFixture.Native)
    :code.delete(LynxFileResourceFixture.Native)
    :code.purge(LynxFileResourceFixture.Native)

    on_exit(fn ->
      :code.delete(LynxFileResourceFixture.Native)
      :code.purge(LynxFileResourceFixture.Native)
    end)

    library = Path.join(tmp, "file-resource-native")
    File.cp!(artifact, library <> ".so")
    source = Path.join(tmp, "native.ex")

    File.write!(source, """
    defmodule LynxFileResourceFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      def checked(_, _), do: :erlang.nif_error(:not_loaded)
      def released(_, _), do: :erlang.nif_error(:not_loaded)
      def file_release(_), do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxFileResourceFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(source, tmp, LynxFileResourceFixture.Native)
  end
end
