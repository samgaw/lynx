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

    options =
      options ++
        [
          proof_modules: ["Record.SharedLogProperties"],
          required_properties:
            ~w(Record.SharedLogProperties.facade_contract Record.SharedLogProperties.critical_contract
              Record.SharedLogProperties.borrow_prefix Record.SharedLogProperties.aliasing_prefix
              Record.SharedLogProperties.full_write)
        ]

    checked = Lynx.Rustler.prepare!(options)

    assert Enum.all?(checked.reports, &(&1.status == :ok)),
           inspect(checked.reports, limit: :infinity)

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
    defmodule LynxIoFixture.Native do
      @on_load :load
      def load, do: :erlang.load_nif(~c"#{native}", 0)
      def commit(_), do: :erlang.nif_error(:not_loaded)
      def log_create, do: :erlang.nif_error(:not_loaded)
      def log_append(_, _), do: :erlang.nif_error(:not_loaded)
    end
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
