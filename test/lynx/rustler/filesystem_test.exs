defmodule Lynx.Rustler.FilesystemTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for native filesystem proofs")

  @tag :tmp_dir
  test "composes a three-crate publication implementation into ordinary Elixir laws", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Publish"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    for {file, name} <- [
          {"PublishProperties", "Properties"},
          {"PayloadProperties", "Payload"},
          {"NamedRecovery", "NamedRecovery"},
          {"WordRecovery", "WordRecovery"},
          {"CommitProperties", "Commit"},
          {"IoErrorProperties", "IoErrors"},
          {"FramedCommitProperties", "Framed"}
        ] do
      source = File.read!(Path.join(@fixture, file <> ".lean"))
      source = String.replace(source, "Lynx io_protocol", "Lynx io_native io_native.io_protocol")
      File.write!(Path.join(project, "Publish/#{name}.lean"), source)
    end

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      lean_project: project,
      module_prefix: "Publish.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_roots: [
        "io_protocol::recover_named_word",
        "io_protocol::open_readonly",
        "io_core::discard_io_error_implicit",
        "io_core::synchronize"
      ]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "commit",
               "arity" => 1,
               "arguments" => ["u16"],
               "result" => "bool",
               "flags" => 2
             } = binding
           ] = prepared.bindings.bindings

    source =
      File.read!(Path.join(@fixture, "NativeCommitProperties.lean"))
      |> String.replace("__COMMIT__", binding["lean_name"])

    File.write!(Path.join(project, "Publish/Native.lean"), source)

    options =
      options ++
        [
          proof_modules:
            ~w(Publish.Properties Publish.Payload Publish.NamedRecovery Publish.WordRecovery Publish.Commit Publish.IoErrors Publish.Framed Publish.Native),
          required_properties: ~w(Publish.Native.facade_prefix Publish.Native.adapter_continuation
        Publish.Commit.Framed.commit_shared Publish.Commit.commit_recovery
        Publish.IoErrors.implicit_cleanup)
        ]

    checked = Lynx.Rustler.prepare!(options)

    assert Enum.all?(checked.reports, &(&1.status == :ok)),
           inspect(checked.reports, limit: :infinity)

    calibrate(prepared, tmp)

    [{_, beam}] = Code.compile_file(Path.join(@fixture, "NativeLaws.exs"))
    law_options = [native: {Lynx.Rustler, options}, initial_environment: "Publish.Commit.initial"]
    reports = Lynx.Laws.verify([beam], law_options)

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(Enum.map(reports, &Map.take(&1, [:module, :status, :diagnostics])),
             limit: :infinity
           )

    assert Enum.any?(reports, &(&1[:initial_environments] == ["Publish.Commit.initial"]))
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

    export = Path.join(tmp, "filesystem.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], law_options ++ [export: export]),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    wrong =
      String.replace(
        File.read!(Path.join(@fixture, "NativeLaws.exs")),
        "commit(513) == true",
        "commit(513) == false"
      )

    [{_, wrong_beam}] = Code.compile_string(wrong)
    assert Enum.any?(Lynx.Laws.verify([wrong_beam], law_options), &(&1.status == :error))

    property = Path.join(project, "Publish/Native.lean")

    for invalid <- [
          "private axiom nativeTrust : False",
          "private theorem unfinishedNative : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> invalid <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, source)

    implementation = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(implementation)
    changed = String.replace(rust, "Ok(complete) => complete", "Ok(_complete) => false")
    refute changed == rust
    File.write!(implementation, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end

  defp calibrate(prepared, tmp) do
    directory = Path.join(tmp, "live-filesystem")
    File.mkdir_p!(directory)
    library = Path.join(directory, "native")
    File.cp!(prepared.library, library <> ".so")
    script = Path.join(directory, "check.exs")

    module_source =
      File.read!(Path.join(@fixture, "Native.exs"))
      |> String.replace("__LIBRARY__", inspect(library))

    File.write!(
      script,
      module_source <>
        """
        for value <- [0, 513, 65535, 65536, 4294967295] do
          true = LynxIoFixture.Native.commit(value)
          expected = <<value::little-unsigned-integer-size(16)>>
          ^expected = File.read!("b")
          false = File.exists?("a")
          :ok = File.rm("b")
        end
        :ok = File.write("a", "occupied")
        false = LynxIoFixture.Native.commit(513)
        for value <- [-1, 4294967296, false] do
          try do
            LynxIoFixture.Native.commit(value)
            raise "accepted invalid input"
          rescue
            ArgumentError -> :ok
          end
        end
        IO.puts("filesystem calibrated")
        """
    )

    {output, status} = System.cmd("elixir", [script], cd: directory, stderr_to_stdout: true)
    assert status == 0, output
    assert output =~ "filesystem calibrated"
    module_path = Path.join(directory, "native.ex")
    File.write!(module_path, module_source)

    assert {:ok, [LynxIoFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(module_path, directory, LynxIoFixture.Native)
  end
end
