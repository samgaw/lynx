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

  defp calibrate_calls(artifact, tmp, write \\ false, commit \\ false) do
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
      def file_write(_, _), do: :erlang.nif_error(:not_loaded)
      def file_write_record(_, _), do: :erlang.nif_error(:not_loaded)
      def file_commit(_), do: :erlang.nif_error(:not_loaded)
      def file_release(_), do: :erlang.nif_error(:not_loaded)
    end
    file = LynxFileResourceFixture.Native.file_create()
    true = is_reference(file)
    #{if write == true do
      """
      for invalid <- [-1, 4294967296] do
        try do
          LynxFileResourceFixture.Native.file_write(file, invalid)
          raise "invalid integer was accepted"
        rescue
          ArgumentError -> :ok
        end
      end
      true = LynxFileResourceFixture.Native.file_write(file, 4660)
      <<52, 18>> = File.read!("resource")
      true = LynxFileResourceFixture.Native.file_write(file, 65536)
      <<52, 18, 0, 0>> = File.read!("resource")
      """
    end}
    #{if write == :record do
      """
      for invalid <- [-1, 4294967296] do
        try do
          LynxFileResourceFixture.Native.file_write_record(file, invalid)
          raise "invalid integer was accepted"
        rescue
          ArgumentError -> :ok
        end
      end
      true = LynxFileResourceFixture.Native.file_write_record(file, 4660)
      <<52, 18, 203, 237>> = File.read!("resource")
      true = LynxFileResourceFixture.Native.file_write_record(file, 65536)
      <<52, 18, 203, 237, 0, 0, 255, 255>> = File.read!("resource")
      """
    end}
    true = LynxFileResourceFixture.Native.file_sync(file)
    {} = LynxFileResourceFixture.Native.file_release(file)
    true = :erlang.garbage_collect()
    true = LynxFileResourceFixture.Native.file_sync(file)
    {} = LynxFileResourceFixture.Native.file_release(file)
    true = LynxFileResourceFixture.Native.file_sync(file)
    #{if commit, do: "true = LynxFileResourceFixture.Native.file_commit(file)"}
    true = File.exists?("resource")
    IO.puts("shared file calls calibrated")
    """)

    {output, status} = System.cmd("elixir", [script], cd: directory, stderr_to_stdout: true)
    assert status == 0, output
    assert output =~ "shared file calls calibrated"
  end

  @tag :tmp_dir
  test "ordinary Elixir creates a verified file resource from an empty namespace", %{tmp_dir: tmp} do
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
      only: [file_create: 0],
      execution: :runtime,
      files: :regular,
      owned_drops: true
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert [%{"name" => "file_create", "arity" => 0, "flags" => 2, "lean_name" => function}] =
             prepared.bindings.bindings

    property = Path.join(project, "FileResource/Creation.lean")

    source =
      File.read!(Path.join(@fixture, "NativeFileResourceCreation.lean"))
      |> String.replace("__CREATE__", function)

    File.write!(property, source)

    options =
      base ++
        [
          proof_modules: ["FileResource.Creation"],
          required_properties:
            ~w(FileResource.Creation.constructor_prefix FileResource.Creation.create_next)
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    load_native(prepared.library, tmp)
    path = Path.join(tmp, "creation.ex")
    File.cp!(Path.join(@fixture, "file_resource_creation.ex"), path)
    [{_, beam}] = Code.compile_file(path)

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        initial_environment: "FileResource.Creation.seed"
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    warm = Lynx.Rustler.prepare!(options)
    assert Enum.all?(warm.reports, &(&1.status == :ok and &1.cached))
    export = Path.join(tmp, "creation.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam],
               native: {Lynx.Rustler, options},
               initial_environment: "FileResource.Creation.seed",
               export: export
             ),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom unfinished : False",
          "private theorem incomplete : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, String.replace(source, "next (.reference 6)", "next (.reference 7)"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property, source)
    native = Path.join(workspace, "native/src/lib.rs")
    original = File.read!(native)

    changed =
      String.replace(
        original,
        "std::fs::File::create_new(\"resource\")",
        "std::fs::File::create_new(\"different\")"
      )

    assert changed != original
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end

  @tag :tmp_dir
  test "ordinary Elixir creates and reuses its verified file resource", %{tmp_dir: tmp} do
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
      only: [file_create: 0, file_release: 1, file_sync: 1],
      execution: :runtime,
      files: :regular,
      owned_drops: true
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert [
             %{"name" => "file_release", "flags" => 2},
             %{"name" => "file_sync", "flags" => 2},
             %{"name" => "file_create", "flags" => 2}
           ] = prepared.bindings.bindings

    for {fixture, module} <- [
          {"NativeFileResourceCreation", "Creation"},
          {"NativeFileResourceCreatedCalls", "CreatedCalls"}
        ] do
      source =
        Enum.reduce(
          prepared.bindings.bindings,
          File.read!(Path.join(@fixture, fixture <> ".lean")),
          fn binding, source ->
            key =
              case binding["name"] do
                "file_create" -> "__CREATE__"
                "file_release" -> "__RELEASE__"
                "file_sync" -> "__SYNC__"
              end

            String.replace(source, key, binding["lean_name"])
          end
        )

      File.write!(Path.join(project, "FileResource/#{module}.lean"), source)
    end

    property = Path.join(project, "FileResource/CreatedCalls.lean")
    source = File.read!(property)

    options =
      base ++
        [
          proof_modules: ["FileResource.Creation", "FileResource.CreatedCalls"],
          required_properties:
            ~w(FileResource.Creation.constructor_prefix FileResource.Creation.create_next
        FileResource.CreatedCalls.release_next FileResource.CreatedCalls.sync_next FileResource.CreatedCalls.create_release_sync)
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    load_native(prepared.library, tmp)
    path = Path.join(tmp, "creation.ex")
    File.cp!(Path.join(@fixture, "file_resource_created_calls.ex"), path)
    [{_, beam}] = Code.compile_file(path)

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        initial_environment: "FileResource.CreatedCalls.seed"
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))
    laws = for %{kind: :elixir_law, status: :verified, theorem: name} <- guarantees, do: name
    assert Enum.sort(laws) == ["create_release_sync/0", "create_sync_release_sync/0"]
    assert Enum.any?(guarantees, &match?(%{kind: :rust_implementation, status: :verified}, &1))
    assert Enum.any?(reports, &(&1[:initial_environments] == ["FileResource.CreatedCalls.seed"]))
    warm = Lynx.Rustler.prepare!(options)
    assert Enum.all?(warm.reports, &(&1.status == :ok and &1.cached))
    export = Path.join(tmp, "creation.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam],
               native: {Lynx.Rustler, options},
               initial_environment: "FileResource.CreatedCalls.seed",
               export: export
             ),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom unfinished : False",
          "private theorem incomplete : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, String.replace(source, "next Term.true", "next Term.false"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property, source)
    native = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(native)

    changed =
      String.replace(
        original,
        "pub fn synchronize_file(file: &std::fs::File) -> std::io::Result<()> {\n    file.sync_all()\n}",
        "pub fn synchronize_file(_file: &std::fs::File) -> std::io::Result<()> {\n    Ok(())\n}"
      )

    assert changed != original
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end

  @tag :tmp_dir
  test "ordinary Elixir writes and synchronizes its created file resource", %{tmp_dir: tmp} do
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
      cargo: [features: ["file-resource-write"]],
      only: [file_create: 0, file_release: 1, file_sync: 1, file_write: 2],
      execution: :runtime,
      files: :regular,
      owned_drops: true
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert [
             %{"name" => "file_release", "flags" => 2},
             %{"name" => "file_sync", "flags" => 2},
             %{"name" => "file_create", "flags" => 2},
             %{"name" => "file_write", "arity" => 2, "flags" => 2}
           ] = prepared.bindings.bindings

    for {fixture, module} <- [
          {"NativeFileResourceCreation", "Creation"},
          {"NativeFileResourceCreatedCalls", "CreatedCalls"},
          {"NativeFileResourceWrite", "Write"}
        ] do
      source =
        Enum.reduce(
          prepared.bindings.bindings,
          File.read!(Path.join(@fixture, fixture <> ".lean")),
          fn binding, source ->
            key =
              case binding["name"] do
                "file_create" -> "__CREATE__"
                "file_release" -> "__RELEASE__"
                "file_sync" -> "__SYNC__"
                "file_write" -> "__WRITE__"
              end

            String.replace(source, key, binding["lean_name"])
          end
        )

      File.write!(Path.join(project, "FileResource/#{module}.lean"), source)
    end

    property = Path.join(project, "FileResource/Write.lean")
    source = File.read!(property)

    options =
      base ++
        [
          proof_modules: [
            "FileResource.Creation",
            "FileResource.CreatedCalls",
            "FileResource.Write"
          ],
          required_properties:
            ~w(FileResource.Creation.constructor_prefix FileResource.Creation.create_next
        FileResource.Write.write_next FileResource.Write.create_write_sync FileResource.Write.short_not_acknowledged)
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    calibrate_calls(prepared.library, tmp, true)
    load_native(prepared.library, tmp)
    path = Path.join(tmp, "creation.ex")
    File.cp!(Path.join(@fixture, "file_resource_write.ex"), path)
    [{_, beam}] = Code.compile_file(path)

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        initial_environment: "FileResource.Write.seed"
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))
    laws = for %{kind: :elixir_law, status: :verified, theorem: name} <- guarantees, do: name
    assert Enum.sort(laws) == ["write_then_sync/1"]
    assert Enum.any?(guarantees, &match?(%{kind: :rust_implementation, status: :verified}, &1))
    assert Enum.any?(reports, &(&1[:initial_environments] == ["FileResource.Write.seed"]))
    warm = Lynx.Rustler.prepare!(options)
    assert Enum.all?(warm.reports, &(&1.status == :ok and &1.cached))
    export = Path.join(tmp, "creation.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam],
               native: {Lynx.Rustler, options},
               initial_environment: "FileResource.Write.seed",
               export: export
             ),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom unfinished : False",
          "private theorem incomplete : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(
      property,
      String.replace(
        source,
        "(synced value).durable = content value",
        "(synced value).durable = ByteArray.empty"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property, source)
    native = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(native)

    changed =
      String.replace(
        original,
        "pub fn synchronize_file(file: &std::fs::File) -> std::io::Result<()> {\n    file.sync_all()\n}",
        "pub fn synchronize_file(_file: &std::fs::File) -> std::io::Result<()> {\n    Ok(())\n}"
      )

    assert changed != original
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(native, original)
    facade = Path.join(workspace, "native/src/lib.rs")
    rust = File.read!(facade)

    incorrect =
      String.replace(rust, "Ok(written) => written == bytes.len()", "Ok(_written) => true")

    assert incorrect != rust
    File.write!(facade, incorrect)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end

  @tag :tmp_dir
  test "ordinary Elixir commits recoverable resource contents and the directory entry", %{
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
      cargo: [features: ["file-resource-commit"]],
      only: [file_create: 0, file_release: 1, file_sync: 1, file_write: 2, file_commit: 1],
      proof_roots: ["effects_native::recover_file_word"],
      execution: :runtime,
      files: :regular,
      owned_drops: true
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert [
             %{"name" => "file_release", "flags" => 2},
             %{"name" => "file_sync", "flags" => 2},
             %{"name" => "file_create", "flags" => 2},
             %{"name" => "file_write", "arity" => 2, "flags" => 2},
             %{"name" => "file_commit", "arity" => 1, "flags" => 2}
           ] = prepared.bindings.bindings

    assert Enum.any?(prepared.extraction.implementations, fn {_, function} ->
             function["rust_name"] == "effects_native::recover_file_word"
           end)

    refute Enum.any?(prepared.bindings.bindings, &(&1["name"] == "recover_file_word"))

    commit = Enum.find(prepared.bindings.bindings, &(&1["name"] == "file_commit"))

    {helper, _} =
      Enum.find(
        prepared.extraction.implementations,
        fn {_, function} -> function["rust_name"] == "effects_native::file_resource_commit" end
      )

    commit_id = commit["definition_id"]

    assert Enum.any?(
             prepared.extraction.native_unwind,
             &match?(
               %{kind: :nonpanicking_borrow_call, caller: ^commit_id, function: ^helper},
               &1
             )
           )

    for {fixture, module} <- [
          {"NativeFileResourceCreation", "Creation"},
          {"NativeFileResourceCreatedCalls", "CreatedCalls"},
          {"NativeFileResourceWrite", "Write"},
          {"NativeFileResourcePublish", "Publish"},
          {"NativeFileResourceRecovery", "Recovery"}
        ] do
      source =
        Enum.reduce(
          prepared.bindings.bindings,
          File.read!(Path.join(@fixture, fixture <> ".lean")),
          fn binding, source ->
            key =
              case binding["name"] do
                "file_create" -> "__CREATE__"
                "file_release" -> "__RELEASE__"
                "file_sync" -> "__SYNC__"
                "file_write" -> "__WRITE__"
                "file_commit" -> "__COMMIT__"
              end

            String.replace(source, key, binding["lean_name"])
          end
        )

      File.write!(Path.join(project, "FileResource/#{module}.lean"), source)
    end

    property = Path.join(project, "FileResource/Publish.lean")
    source = File.read!(property)

    options =
      base ++
        [
          proof_modules: [
            "FileResource.Creation",
            "FileResource.CreatedCalls",
            "FileResource.Write",
            "FileResource.Publish",
            "FileResource.Recovery"
          ],
          required_properties:
            ~w(FileResource.Creation.constructor_prefix FileResource.Creation.create_next
        FileResource.Write.write_next FileResource.Publish.directory_prefix
        FileResource.Publish.commit_next FileResource.Publish.acknowledged_crash
        FileResource.Recovery.recover_admitted FileResource.Recovery.commit_recovery
        FileResource.Recovery.read_error_cleanup FileResource.Recovery.phase_prefix
        FileResource.Recovery.phase_retry FileResource.Recovery.finite_retries
        FileResource.Recovery.nonempty_retry FileResource.Recovery.committed_retries)
        ]

    checked = Lynx.Rustler.prepare!(options)
    assert Enum.all?(checked.reports, &(&1.status == :ok))
    calibrate_calls(prepared.library, tmp, true, true)
    load_native(prepared.library, tmp)
    path = Path.join(tmp, "creation.ex")
    File.cp!(Path.join(@fixture, "file_resource_publish.ex"), path)
    [{_, beam}] = Code.compile_file(path)

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        initial_environment: "FileResource.Publish.seed"
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))
    laws = for %{kind: :elixir_law, status: :verified, theorem: name} <- guarantees, do: name
    assert Enum.sort(laws) == ["write_then_commit/1"]
    assert Enum.any?(guarantees, &match?(%{kind: :rust_implementation, status: :verified}, &1))
    assert Enum.any?(reports, &(&1[:initial_environments] == ["FileResource.Publish.seed"]))
    warm = Lynx.Rustler.prepare!(options)
    assert Enum.all?(warm.reports, &(&1.status == :ok and &1.cached))
    export = Path.join(tmp, "creation.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam],
               native: {Lynx.Rustler, options},
               initial_environment: "FileResource.Publish.seed",
               export: export
             ),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom unfinished : False",
          "private theorem incomplete : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(
      property,
      String.replace(
        source,
        "image.inodes = [(1,Write.content value)]",
        "image.inodes = []"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property, source)
    recovery_property = Path.join(project, "FileResource/Recovery.lean")
    recovery_source = File.read!(recovery_property)

    for false_recovery <- [
          String.replace(recovery_source, "(.ok (.Ok (some value))", "(.ok (.Ok none)"),
          String.replace(
            recovery_source,
            "refCounter := generation + 1",
            "refCounter := generation"
          ),
          String.replace(
            recovery_source,
            "| .beforeSecondRead => scan low high generation 1",
            "| .beforeSecondRead => scan low high generation 2"
          )
        ] do
      assert false_recovery != recovery_source
      File.write!(recovery_property, false_recovery)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(recovery_property, recovery_source)
    native = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(native)

    changed =
      String.replace(
        original,
        "    directory.sync_all()\n",
        "    let _ = directory;\n    Ok(())\n"
      )

    assert changed != original
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(native, original)

    incorrect_parser =
      String.replace(
        original,
        "u16::from_le_bytes([low, high])",
        "u16::from_be_bytes([low, high])"
      )

    assert incorrect_parser != original
    File.write!(native, incorrect_parser)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(native, original)

    panic =
      String.replace(
        original,
        "    directory.sync_all()\n",
        "    let _ = directory;\n    panic!()\n"
      )

    assert panic != original
    File.write!(native, panic)
    assert_raise CompileError, ~r/drop|panic|unwind/, fn -> Lynx.Rustler.prepare!(options) end
  end

  @tag :tmp_dir
  @tag :checked_record
  test "checked resource records reject torn values before commitment", %{tmp_dir: tmp} do
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
      cargo: [features: ["file-resource-record"]],
      only: [
        file_create: 0,
        file_release: 1,
        file_sync: 1,
        file_write: 2,
        file_commit: 1,
        file_write_record: 2
      ],
      proof_roots: [
        "effects_native::recover_file_word",
        "effects_native::recover_file_record",
        "effects_core::synchronize_directory"
      ],
      execution: :runtime,
      files: :regular,
      owned_drops: true
    ]

    prepared = Lynx.Rustler.prepare!(base)

    assert %{"name" => "file_write_record", "arity" => 2, "flags" => 2, "result" => "bool"} =
             Enum.find(prepared.bindings.bindings, &(&1["name"] == "file_write_record"))

    assert length(prepared.bindings.bindings) == 6

    {recovery, _} =
      Enum.find(prepared.extraction.implementations, fn {_, f} ->
        f["rust_name"] == "effects_native::recover_file_record"
      end)

    {reader, _} =
      Enum.find(prepared.extraction.implementations, fn {_, f} ->
        f["rust_name"] == "effects_core::read_file_record"
      end)

    assert Enum.any?(
             prepared.extraction.native_unwind,
             &match?(%{kind: :nonpanicking_borrow_call, caller: ^recovery, function: ^reader}, &1)
           )

    modules =
      ~w(Creation CreatedCalls Write Publish Recovery Record RecordRecovery ShortRecovery RecordRetry RecordErrors RecordCleanup CommitPhases CallPrefix CommitFailure)

    replacements = %{
      "file_create" => "__CREATE__",
      "file_release" => "__RELEASE__",
      "file_sync" => "__SYNC__",
      "file_write" => "__WRITE__",
      "file_commit" => "__COMMIT__",
      "file_write_record" => "__WRITE_RECORD__"
    }

    for module <- modules do
      source =
        Enum.reduce(
          prepared.bindings.bindings,
          File.read!(Path.join(@fixture, "NativeFileResource#{module}.lean")),
          fn binding, source ->
            String.replace(
              source,
              Map.fetch!(replacements, binding["name"]),
              binding["lean_name"]
            )
          end
        )

      File.write!(Path.join(project, "FileResource/#{module}.lean"), source)
    end

    options =
      base ++
        [
          proof_modules: Enum.map(modules, &("FileResource." <> &1)),
          required_properties: ~w(FileResource.Record.encode_spec FileResource.Record.decode_spec
        FileResource.Record.torn_decode FileResource.Record.decode_layout FileResource.Record.write_next
        FileResource.Record.short_not_acknowledged FileResource.Record.create_write_commit
        FileResource.RecordRecovery.recover_record FileResource.RecordRecovery.recover_value
        FileResource.RecordRecovery.torn_recovery FileResource.RecordRecovery.create_write
        FileResource.RecordRecovery.uncommitted_write_recovery
        FileResource.ShortRecovery.recover_short FileResource.ShortRecovery.recover_bytes
        FileResource.ShortRecovery.uncommitted_short_recovery FileResource.ShortRecovery.short_witness
        FileResource.ShortRecovery.missing_recovery FileResource.ShortRecovery.uncommitted_missing_recovery
        FileResource.ShortRecovery.named_image_recovery FileResource.ShortRecovery.all_image_recovery
        FileResource.ShortRecovery.create_partial FileResource.ShortRecovery.partial_write_recovery
        FileResource.ShortRecovery.partial_missing_recovery
        FileResource.RecordRetry.phase_prefix FileResource.RecordRetry.phase_retry
        FileResource.RecordRetry.finite_retries FileResource.RecordRetry.nonempty_retry
        FileResource.RecordRetry.committed_retries FileResource.RecordRetry.transaction_retries
        FileResource.RecordErrors.record_error FileResource.RecordErrors.recover_error
        FileResource.RecordErrors.recover_complete FileResource.RecordErrors.committed_error
        FileResource.RecordErrors.error_then_retries FileResource.RecordErrors.error_crash_witness
        FileResource.RecordErrors.finite_attempts FileResource.RecordErrors.committed_attempts
        FileResource.RecordErrors.one_failed_attempt
        FileResource.RecordErrors.open_failure_prefix FileResource.RecordErrors.recover_open_failure
        FileResource.RecordErrors.committed_open_failure FileResource.RecordErrors.opening_retry
        FileResource.RecordErrors.opening_witness
        FileResource.RecordCleanup.before_close FileResource.RecordCleanup.after_close
        FileResource.RecordCleanup.cleanup_prefix FileResource.RecordCleanup.cleanup_retry
        FileResource.RecordCleanup.cleanup_witness FileResource.RecordCleanup.transaction_attempts
        FileResource.ShortRecovery.persisted_image_recovery
        FileResource.CommitPhases.phase_prefix FileResource.CommitPhases.phase_recovery
        FileResource.CommitPhases.post_sync_recovery FileResource.CommitPhases.directory_sync_recovery
        FileResource.CommitPhases.phase_witness FileResource.CommitPhases.lost_name_witness
        FileResource.CommitPhases.nif_phase_prefix FileResource.CommitPhases.nif_phase_recovery
        FileResource.CommitPhases.complete_prefix
        FileResource.CallPrefix.release_prefix FileResource.CallPrefix.facade_prefix
        FileResource.CallPrefix.call_run FileResource.CallPrefix.boundary_recovery
        FileResource.CallPrefix.acknowledged_retries
        FileResource.CommitFailure.commit_prefix FileResource.CommitFailure.release_prefix
        FileResource.CommitFailure.facade_prefix FileResource.CommitFailure.call_run
        FileResource.CommitFailure.failure_env FileResource.CommitFailure.retry_run)
        ]

    verified = Lynx.Rustler.prepare!(options)
    assert Enum.all?(verified.reports, &(&1.status == :ok))
    calibrate_calls(prepared.library, tmp, :record, true)
    load_native(prepared.library, tmp)
    path = Path.join(tmp, "record.ex")
    File.cp!(Path.join(@fixture, "file_resource_record.ex"), path)
    [{_, beam}] = Code.compile_file(path)

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        initial_environment: "FileResource.Record.recordSeed"
      )

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    assert [%{kind: :elixir_law, status: :verified, theorem: "record_then_commit/1"}] =
             Enum.filter(guarantees, &(&1.kind == :elixir_law))

    short_path = Path.join(tmp, "short_record.ex")
    File.cp!(Path.join(@fixture, "file_resource_short.ex"), short_path)
    [{_, short_beam}] = Code.compile_file(short_path)

    short_reports =
      Lynx.Laws.verify([short_beam],
        native: {Lynx.Rustler, options},
        initial_environment: "FileResource.ShortRecovery.seed"
      )

    assert Enum.all?(short_reports, &(&1.status == :ok)), inspect(short_reports, limit: :infinity)

    short_laws =
      for report <- short_reports,
          %{kind: :elixir_law, status: :verified, theorem: name} <- report[:guarantees] || [],
          do: name

    assert short_laws == ["short_record_not_committed/1"]
    failure_path = Path.join(tmp, "failed_commit.ex")
    File.cp!(Path.join(@fixture, "file_resource_failure.ex"), failure_path)
    [{_, failure_beam}] = Code.compile_file(failure_path)

    failure_reports =
      Lynx.Laws.verify([failure_beam],
        native: {Lynx.Rustler, options},
        initial_environment: "FileResource.CommitFailure.seed"
      )

    assert Enum.all?(failure_reports, &(&1.status == :ok)),
           inspect(failure_reports, limit: :infinity)

    assert ["failed_sync_can_retry/0"] ==
             for(
               report <- failure_reports,
               %{kind: :elixir_law, status: :verified, theorem: name} <- report[:guarantees] || [],
               do: name
             )

    warm = Lynx.Rustler.prepare!(options)
    assert Enum.all?(warm.reports, &(&1.status == :ok and &1.cached))
    export = Path.join(tmp, "record.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam],
               native: {Lynx.Rustler, options},
               initial_environment: "FileResource.Record.recordSeed",
               export: export
             ),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    property = Path.join(project, "FileResource/RecordRecovery.lean")
    source = File.read!(property)

    for extra <- [
          "private axiom unfinished : False",
          "private theorem incomplete : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    false_contract = String.replace(source, "true) ∨", "true) ∧")
    assert false_contract != source
    File.write!(property, false_contract)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property, source)
    short_property = Path.join(project, "FileResource/ShortRecovery.lean")
    short_source = File.read!(short_property)

    for wrong <- [
          String.replace(short_source, "(.ok (.Ok none),scan", "(.ok (.Ok (some 0#u16)),scan"),
          String.replace(
            short_source,
            "(.ok (.Err ⟨error⟩),missingDone",
            "(.ok (.Err ⟨error + 1⟩),missingDone"
          )
        ] do
      assert wrong != short_source
      File.write!(short_property, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(short_property, short_source)
    retry_property = Path.join(project, "FileResource/RecordRetry.lean")
    retry_source = File.read!(retry_property)

    wrong_retry =
      String.replace(retry_source, "(.ok (.Ok (some value)),scan", "(.ok (.Ok none),scan")

    assert wrong_retry != retry_source
    File.write!(retry_property, wrong_retry)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(retry_property, retry_source)
    error_property = Path.join(project, "FileResource/RecordErrors.lean")
    error_source = File.read!(error_property)

    for wrong <- [
          String.replace(
            error_source,
            "(.ok (.Err ⟨error⟩),scan",
            "(.ok (.Err ⟨error + 1⟩),scan"
          ),
          String.replace(error_source, "position .nil true)", "position .nil false)"),
          String.replace(
            error_source,
            "(.ok (.Err ⟨error⟩),checkpoint",
            "(.ok (.Err ⟨error + 1⟩),checkpoint"
          ),
          String.replace(
            error_source,
            "checkpoint contents generation .nil)",
            "checkpoint contents (generation + 1) .nil)"
          )
        ] do
      assert wrong != error_source
      File.write!(error_property, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(error_property, error_source)
    cleanup_property = Path.join(project, "FileResource/RecordCleanup.lean")
    cleanup_source = File.read!(cleanup_property)

    premature_close =
      String.replace(
        cleanup_source,
        "(cleanup generation error) (scan a b c d generation position (closing closeError))",
        "(cleanup generation error) (scan a b c d generation position .nil true)"
      )

    assert premature_close != cleanup_source
    File.write!(cleanup_property, premature_close)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(cleanup_property, cleanup_source)
    phases_property = Path.join(project, "FileResource/CommitPhases.lean")
    phases_source = File.read!(phases_property)

    premature_namespace =
      String.replace(
        phases_source,
        "(image.names = [] ∨ image.names = Publish.names) ∧",
        "image.names = Publish.names ∧"
      )

    assert premature_namespace != phases_source
    File.write!(phases_property, premature_namespace)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(phases_property, phases_source)
    call_property = Path.join(project, "FileResource/CallPrefix.lean")
    call_source = File.read!(call_property)

    for wrong <- [
          String.replace(call_source, ".reference 6", ".reference 5"),
          String.replace(
            call_source,
            "(Record.done env value)",
            "(CommitPhases.phaseEnv env value .finished)"
          )
        ] do
      assert wrong != call_source
      File.write!(call_property, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(call_property, call_source)
    failure_property = Path.join(project, "FileResource/CommitFailure.lean")
    failure_source = File.read!(failure_property)

    for wrong <- [
          String.replace(failure_source, "(.ok false) (done", "(.ok true) (done"),
          String.replace(
            failure_source,
            "Record.content value,saved,4,rest",
            "Record.content value,ByteArray.empty,4,rest"
          ),
          String.replace(
            failure_source,
            "(10,NativeIoError.typeName,.atom \"live\")",
            "(10,NativeIoError.typeName,.atom \"stale\")"
          )
        ] do
      assert wrong != failure_source
      File.write!(failure_property, wrong)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(failure_property, failure_source)
    native = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(native)

    for changed <- [
          String.replace(rust, "(!value).to_le_bytes()", "value.to_le_bytes()"),
          String.replace(rust, "value ^ inverse == u16::MAX", "value ^ inverse != u16::MAX"),
          String.replace(rust, "Ok(None) => Ok(None),", "Ok(None) => Ok(Some(0)),"),
          String.replace(rust, "Err(error) => Err(error),", "Err(_error) => Ok(None),")
        ] do
      assert changed != rust
      File.write!(native, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(native, rust)
    facade = Path.join(workspace, "native/src/lib.rs")
    facade_source = File.read!(facade)

    swallowed_open_error =
      String.replace(
        facade_source,
        "pub fn recover_file_record(path: &str) -> std::io::Result<Option<u16>> {\n    let mut file = std::fs::File::open(path)?;",
        String.trim_trailing("""
        pub fn recover_file_record(path: &str) -> std::io::Result<Option<u16>> {
            let mut file = match std::fs::File::open(path) {
                Ok(file) => file,
                Err(_error) => return Ok(None),
            };
        """)
      )

    acknowledged_error =
      String.replace(
        facade_source,
        "let outcome = file_resource_commit(&resource);\n    file_resource_release(resource);\n    match outcome {\n        Ok(()) => true,\n        Err(error) => {\n            drop(error);\n            false",
        "let outcome = file_resource_commit(&resource);\n    file_resource_release(resource);\n    match outcome {\n        Ok(()) => true,\n        Err(error) => {\n            drop(error);\n            true"
      )

    for changed <- [
          acknowledged_error,
          swallowed_open_error,
          String.replace(
            facade_source,
            "    file_resource_sync(resource)?;",
            "    let _ = resource;"
          ),
          String.replace(
            facade_source,
            "    effects_core::synchronize_directory()\n}",
            "    Ok(())\n}"
          )
        ] do
      assert changed != facade_source
      File.write!(facade, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end
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
      def file_write(_, _), do: :erlang.nif_error(:not_loaded)
      def file_write_record(_, _), do: :erlang.nif_error(:not_loaded)
      def file_commit(_), do: :erlang.nif_error(:not_loaded)
      def file_create, do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxFileResourceFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(source, tmp, LynxFileResourceFixture.Native)
  end
end
