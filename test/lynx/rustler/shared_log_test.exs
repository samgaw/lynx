defmodule Lynx.Rustler.SharedLogTest do
  use ExUnit.Case
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for shared file resource proofs")
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)

  @tag :tmp_dir
  test "links a shared resource facade to cross-crate append and rollback implementations", %{
    tmp_dir: tmp
  } do
    {workspace, project, fixture_options} = Lynx.Rust.IoFixture.prepare!(tmp, @tools)

    # Reuse the same implementation properties under the facade's Cargo root.
    # Owned extraction invokes the checked guard destructor dispatch.
    for module <- fixture_options[:proof_modules] do
      path = Path.join(project, String.replace(module, ".", "/") <> ".lean")

      source =
        File.read!(path)
        |> String.replace("Lynx io_protocol", "Lynx io_native io_native.io_protocol")
        |> String.replace("NativeDrop.drop", "NativeOwnedDrop.drop")

      File.write!(path, source)
    end

    options = [
      workspace: workspace,
      package: "io-native",
      tools: @tools,
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      cargo: [features: ["shared-log"]],
      only: [log_create: 0, log_append: 2],
      proof_roots: fixture_options[:roots],
      lean_project: project,
      module_prefix: "Record.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{"name" => "log_create", "arity" => 0, "flags" => 2},
             %{"name" => "log_append", "arity" => 2, "flags" => 2} = append
           ] = prepared.bindings.bindings

    calibrate(prepared.library, tmp)

    source =
      File.read!(Path.join(@fixture, "SharedLogProperties.lean"))
      |> String.replace("__APPEND__", append["lean_name"])

    proof = Path.join(project, "Record/SharedLogProperties.lean")
    File.write!(proof, source)

    for module <- ~w(FramedLogProperties NativeLogProperties) do
      text =
        File.read!(Path.join(@fixture, module <> ".lean"))
        |> String.replace("__APPEND__", append["lean_name"])

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), text)
    end

    options =
      options ++
        [
          proof_modules:
            ~w(Record.SharedLogProperties Record.FramedLogProperties Record.NativeLogProperties),
          required_properties:
            ~w(Record.SharedLogProperties.facade_contract Record.SharedLogProperties.critical_contract
              Record.SharedLogProperties.borrow_prefix Record.SharedLogProperties.aliasing_prefix
              Record.SharedLogProperties.full_write Record.FramedLogProperties.append_success
              Record.NativeLogProperties.append_prefix Record.NativeLogProperties.facade_prefix
              Record.NativeLogProperties.adapter_continuation Record.NativeLogProperties.initial_adapter)
        ]

    checked = Lynx.Rustler.prepare!(options)

    assert Enum.all?(checked.reports, &(&1.status == :ok)),
           inspect(checked.reports, limit: :infinity)

    Code.compile_file(Path.join(@fixture, "NativeLogBindings.exs"))
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "NativeLogLaws.exs"))

    law_options = [
      native: {Lynx.Rustler, options},
      initial_environment: "Record.NativeLogProperties.initial"
    ]

    reports = Lynx.Laws.verify([beam], law_options)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

    assert Enum.any?(
             reports,
             &(&1[:initial_environments] == ["Record.NativeLogProperties.initial"])
           )

    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

    export = Path.join(tmp, "shared-log.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], law_options ++ [export: export]),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    wrong =
      File.read!(Path.join(@fixture, "NativeLogLaws.exs"))
      |> String.replace("value) == true", "value) == false")

    [{_, wrong_beam}] = Code.compile_string(wrong)
    assert Enum.any?(Lynx.Laws.verify([wrong_beam], law_options), &(&1.status == :error))

    native_proof = Path.join(project, "Record/NativeLogProperties.lean")
    native_source = File.read!(native_proof)

    leaked =
      String.replace(native_source, "framedEnv env 8 pinnedFrame", "framedEnv env 8 decodedFrame")

    refute leaked == native_source
    File.write!(native_proof, leaked)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    for invalid <- [
          "private axiom logAssumption : False",
          "private theorem unfinishedLogCall : True := by sorry"
        ] do
      File.write!(native_proof, native_source <> "\n" <> invalid <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(native_proof, native_source)

    # A complete synchronized write cannot be reported as rejected.
    File.write!(proof, String.replace(source, "(.ok (.Ok true)) s5", "(.ok (.Ok false)) s5"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(proof, source)

    # Changing the actual Rust critical section invalidates the facade contract.
    rust = Path.join(workspace, "native/src/lib.rs")
    implementation = File.read!(rust)

    File.write!(
      rust,
      String.replace(
        implementation,
        "io_protocol::locked_append_or_rollback(&resource.file, value)",
        "Ok(value == 0)"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end

  defp calibrate(library, tmp) do
    directory = Path.join(tmp, "live-log")
    File.mkdir_p!(directory)
    native = Path.join(directory, "native")
    File.cp!(library, native <> ".so")
    script = Path.join(directory, "check.exs")

    File.write!(script, """
    Code.require_file(#{inspect(Path.join(@fixture, "NativeLogBindings.exs"))})
    :ok = LynxIoFixture.Native.load(~c"#{native}")
    resource = LynxIoFixture.Native.log_create()
    true = LynxIoFixture.Native.log_append(resource, 123)
    true = LynxIoFixture.Native.log_append(resource, 65_535)
    true = LynxIoFixture.Native.log_append(resource, 65_536)
    <<123::little-16, 65_412::little-16, 65_535::little-16, 0::little-16,
      0::little-16, 65_535::little-16>> = File.read!("journal")
    for invalid <- [-1, 4_294_967_296] do
      try do
        LynxIoFixture.Native.log_append(resource, invalid)
        raise "accepted an out-of-range Rustler unsigned input"
      rescue
        ArgumentError -> :ok
      end
    end
    """)

    {output, status} = System.cmd("elixir", [script], cd: directory, stderr_to_stdout: true)
    assert status == 0, output
  end
end
