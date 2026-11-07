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

  @tag :tmp_dir
  test "ordinary Elixir calls retain a shared file through release and synchronization", %{
    tmp_dir: tmp
  } do
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
      cargo: [features: ["file-resource-sync"]],
      only: [file_release: 1, file_sync: 1],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      proof_roots: [
        "effects_native::file_resource_clone",
        "effects_native::file_resource_new",
        "effects_native::file_resource_cycle",
        "effects_native::file_resource_sync"
      ]
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert [%{"name" => "file_release", "flags" => 2}, %{"name" => "file_sync", "flags" => 2}] =
             prepared.bindings.bindings

    for {source, target} <- [
          {"NativeFileResourceModel", "Model"},
          {"NativeFileResource", "Properties"},
          {"NativeFileResourceNif", "NifProperties"},
          {"NativeFileResourceCalls", "Calls"}
        ] do
      contents = File.read!(Path.join(@fixture, source <> ".lean"))

      contents =
        Enum.reduce(
          [{"file_release", "__RELEASE__"}, {"file_sync", "__SYNC__"}],
          contents,
          fn {name, placeholder}, contents ->
            binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
            String.replace(contents, placeholder, binding["lean_name"])
          end
        )

      File.write!(Path.join(project, "FileResource/#{target}.lean"), contents)
    end

    options =
      base ++
        [
          proof_modules:
            ~w(FileResource.Model FileResource.Properties FileResource.NifProperties FileResource.Calls),
          required_properties:
            ~w(FileResource.Properties.cleanup_contract FileResource.Properties.clone_next
        FileResource.Properties.retained_release_next FileResource.Properties.retained_final_release_next
        FileResource.Properties.complete_cycle FileResource.Properties.cycle_keeps_disk
        FileResource.Calls.release_next FileResource.Calls.sync_next FileResource.Calls.release_sync_protocol)
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))

    assert Enum.any?(
             checked.verification.unverified_nif_exports,
             &match?(%{function: "file_create", arity: 0, status: :unverified}, &1)
           )

    calibrate_calls(prepared.library, tmp)
    load_native(prepared.library, tmp)
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "file_resource_calls.ex"))

    law_options = [
      native: {Lynx.Rustler, options},
      initial_environment: "FileResource.Calls.seed"
    ]

    reports = Lynx.Laws.verify([beam], law_options)

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(Enum.filter(reports, &(&1.status != :ok)), limit: :infinity)

    assert Enum.any?(reports, &(&1[:initial_environments] == ["FileResource.Calls.seed"]))
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
    export = Path.join(tmp, "file-calls.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], law_options ++ [export: export]),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    # The live calibration constructor is deliberately outside the verified selection.
    [{_, unselected}] =
      Code.compile_string(~S"""
      defmodule LynxEffectsFixture.UnselectedFileCalls do
        @compile :debug_info
        use Lynx.Laws
        law constructor, expects: is_reference(LynxFileResourceFixture.Native.file_create()), proof: ~LEAN"rfl"
      end
      """)

    assert_raise CompileError, ~r/unregistered external implementation/, fn ->
      Lynx.Laws.verify([unselected], externals: [checked.external], lean_project: project)
    end

    property = Path.join(project, "FileResource/Calls.lean")
    original = File.read!(property)

    for extra <- [
          "private axiom fileCallsTrust : False",
          "private theorem unfinishedFileCalls : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, original)
    wrong = String.replace(original, "twice.durable = ⟨#[2]⟩", "twice.durable = ⟨#[1]⟩")
    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)

    native = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(native)

    changed =
      String.replace(
        rust,
        "pub fn synchronize_file(file: &std::fs::File) -> std::io::Result<()> {\n    file.sync_all()\n}",
        "pub fn synchronize_file(_file: &std::fs::File) -> std::io::Result<()> {\n    Ok(())\n}"
      )

    refute changed == rust
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end

  defp calibrate_calls(artifact, tmp) do
    directory = Path.join(tmp, "live-file-calls")
    File.mkdir_p!(directory)
    library = Path.join(directory, "native")
    File.cp!(artifact, library <> ".so")
    script = Path.join(directory, "calls.exs")

    File.write!(script, """
    defmodule LynxFileResourceFixture.Native do
      @on_load :load
      def load, do: :erlang.load_nif(~c"#{library}",0)
      def checked(_,_), do: :erlang.nif_error(:not_loaded)
      def released(_,_), do: :erlang.nif_error(:not_loaded)
      def file_create, do: :erlang.nif_error(:not_loaded)
      def file_sync(_), do: :erlang.nif_error(:not_loaded)
      def file_release(_), do: :erlang.nif_error(:not_loaded)
    end
    file = LynxFileResourceFixture.Native.file_create()
    true = is_reference(file)
    true = LynxFileResourceFixture.Native.file_sync(file)
    {} = LynxFileResourceFixture.Native.file_release(file)
    true = :erlang.garbage_collect()
    true = LynxFileResourceFixture.Native.file_sync(file)
    {} = LynxFileResourceFixture.Native.file_release(file)
    true = LynxFileResourceFixture.Native.file_sync(file)
    true = File.exists?("resource")
    IO.puts("shared file calls calibrated")
    """)

    {output, status} = System.cmd("elixir", [script], cd: directory, stderr_to_stdout: true)
    assert status == 0, output
    assert output =~ "shared file calls calibrated"
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
      def file_sync(_), do: :erlang.nif_error(:not_loaded)
      def file_create, do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxFileResourceFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(source, tmp, LynxFileResourceFixture.Native)
  end
end
