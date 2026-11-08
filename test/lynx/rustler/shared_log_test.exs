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

    for module <-
          ~w(FramedLogProperties NativeLogProperties OverlappingLogProperties ScheduledLogProperties RegisteredLogProperties ContendedLogProperties) do
      text =
        File.read!(Path.join(@fixture, module <> ".lean"))
        |> String.replace("__APPEND__", append["lean_name"])

      File.write!(Path.join(project, "Record/" <> module <> ".lean"), text)
    end

    options =
      options ++
        [
          proof_modules:
            ~w(Record.SharedLogProperties Record.FramedLogProperties Record.NativeLogProperties Record.OverlappingLogProperties Record.ScheduledLogProperties Record.RegisteredLogProperties Record.ContendedLogProperties),
          required_properties:
            ~w(Record.SharedLogProperties.facade_contract Record.SharedLogProperties.critical_contract
              Record.SharedLogProperties.borrow_prefix Record.SharedLogProperties.aliasing_prefix
              Record.SharedLogProperties.full_write Record.FramedLogProperties.append_success
              Record.NativeLogProperties.append_prefix Record.NativeLogProperties.facade_prefix
              Record.NativeLogProperties.adapter_continuation Record.NativeLogProperties.initial_adapter
              Record.FramedLogProperties.guarded_prefix Record.OverlappingLogProperties.caller_contract
              Record.OverlappingLogProperties.acquired_prefix Record.OverlappingLogProperties.second_call
              Record.OverlappingLogProperties.overlap_phases Record.ScheduledLogProperties.call_steps
              Record.ScheduledLogProperties.scheduled_calls Record.ScheduledLogProperties.scheduled_records
              Record.RegisteredLogProperties.call_steps Record.RegisteredLogProperties.decoded_call_steps
              Record.ContendedLogProperties.decoded_lock_prefix)
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

    scheduler_export = Path.join(tmp, "native-scheduler.export")

    adapter_source = File.read!(Path.join(@fixture, "RegisteredAdapterProperties.lean"))

    adapter_file = %{
      "module" => "Record.RegisteredAdapterProperties",
      "file" => "Record.RegisteredAdapterProperties.lean",
      "imports" => ["Record.Extraction.RustlerAdapter", "Record.RegisteredLogProperties"],
      "contents" => [],
      "audit_modules" => [
        "Record.RegisteredAdapterProperties",
        "Record.RegisteredLogProperties"
      ],
      "preludes" => [
        %{
          "source" => adapter_source,
          "file" => "Record.RegisteredAdapterProperties.lean",
          "span" => [1],
          "indentation" => 0
        }
      ]
    }

    native_files =
      Lynx.Translation.new(externals: [checked.external]) |> Lynx.Translation.assemble()

    contended_source = File.read!(Path.join(@fixture, "ContendedAdapterProperties.lean"))
    [adapter_prelude] = adapter_file["preludes"]

    contended_file = %{
      adapter_file
      | "module" => "Record.ContendedAdapterProperties",
        "file" => "Record.ContendedAdapterProperties.lean",
        "imports" => ["Record.RegisteredAdapterProperties", "Record.ContendedLogProperties"],
        "audit_modules" => ["Record.ContendedAdapterProperties", "Record.ContendedLogProperties"],
        "preludes" => [
          %{
            adapter_prelude
            | "source" => contended_source,
              "file" => "Record.ContendedAdapterProperties.lean"
          }
        ]
    }

    scheduler_file = %{
      "module" => "Record.SchedulerExport",
      "file" => "Record.SchedulerExport.lean",
      "imports" => [
        "Record.ScheduledLogProperties",
        "Record.RegisteredAdapterProperties",
        "Record.ContendedAdapterProperties"
      ],
      "contents" => [],
      "audit_modules" => [
        "Record.ScheduledLogProperties",
        "Record.NativeRuntime",
        "Lynx.Term.Runner"
      ],
      "preludes" => [
        %{
          "source" => """
          module
          public import Record.ScheduledLogProperties
          public import Record.RegisteredAdapterProperties
          public import Record.ContendedAdapterProperties
          public def checkedSchedulerWitness := Record.ScheduledLogProperties.scheduled_records
          public def checkedRegisteredWitness := Record.RegisteredAdapterProperties.registered_records
          public def checkedContendedWitness := Record.ContendedAdapterProperties.contended_records
          """,
          "file" => "Record.SchedulerExport.lean",
          "span" => [1],
          "indentation" => 0
        }
      ]
    }

    assert Enum.all?(
             Lynx.Commands.verify!(
               project,
               native_files ++ [adapter_file, contended_file, scheduler_file],
               export: scheduler_export
             ),
             &(&1.status == :ok)
           )

    assert File.read!(scheduler_export) =~ "scheduled_records"
    assert File.read!(scheduler_export) =~ "registered_records"
    assert File.read!(scheduler_export) =~ "contended_records"

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", scheduler_export] ++ sandbox)

    assert status == 0, output

    for incorrect <- [
          String.replace(contended_source, "refCounter := 10", "refCounter := 11"),
          String.replace(contended_source, "body_steps 1 true 9 8", "body_steps 1 true 9 9"),
          String.replace(contended_source, "(.integer 19)", "(.integer 20)"),
          contended_source <> "\nprivate axiom unchecked_native_claim : False\n",
          contended_source <> "\nprivate theorem unfinished_native_claim : False := by sorry\n"
        ] do
      refute incorrect == contended_source
      [prelude] = contended_file["preludes"]
      wrong = %{contended_file | "preludes" => [%{prelude | "source" => incorrect}]}

      assert Enum.any?(
               Lynx.Commands.verify!(project, native_files ++ [adapter_file, wrong]),
               &(&1.module == "Record.ContendedAdapterProperties" and &1.status == :error)
             )
    end

    for incorrect <- [
          String.replace(adapter_source, "refCounter := 10", "refCounter := 11"),
          String.replace(adapter_source, "(.integer 19)", "(.integer 20)"),
          String.replace(
            adapter_source,
            "[NativeResourceArc.typeName shared_log.LogResource]",
            "[]"
          )
        ] do
      refute incorrect == adapter_source
      [prelude] = adapter_file["preludes"]
      wrong = %{adapter_file | "preludes" => [%{prelude | "source" => incorrect}]}

      assert Enum.any?(
               Lynx.Commands.verify!(project, native_files ++ [wrong]),
               &(&1.module == "Record.RegisteredAdapterProperties" and &1.status == :error)
             )
    end

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

    overlapping_proof = Path.join(project, "Record/OverlappingLogProperties.lean")
    overlapping_source = File.read!(overlapping_proof)

    for incorrect <- [
          String.replace(
            overlapping_source,
            "NativeGuard.pollRelease (guard env 7)",
            "NativeGuard.pollRelease (guard env 8)"
          ),
          String.replace(
            overlapping_source,
            ".tuple #[.integer 2, NativeCodec.encode logPayload]) else cell",
            ".tuple #[.integer 1, NativeCodec.encode logPayload]) else cell"
          )
        ] do
      refute incorrect == overlapping_source
      File.write!(overlapping_proof, incorrect)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rustler.prepare!(options)
        end

      assert error.message =~ "Record/OverlappingLogProperties.lean:"
    end

    File.write!(overlapping_proof, overlapping_source)

    scheduled_proof = Path.join(project, "Record/ScheduledLogProperties.lean")
    scheduled_source = File.read!(scheduled_proof)

    for incorrect <- [
          String.replace(scheduled_source, "refCounter := 11", "refCounter := 12"),
          String.replace(
            scheduled_source,
            "overwrite ByteArray.empty 0 (bytes (payload 13#u16)) 4",
            "overwrite ByteArray.empty 0 (bytes (payload 19#u16)) 4"
          )
        ] do
      refute incorrect == scheduled_source
      File.write!(scheduled_proof, incorrect)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rustler.prepare!(options)
        end

      assert error.message =~ "Record/ScheduledLogProperties.lean:"
    end

    File.write!(scheduled_proof, scheduled_source)

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
    writers = for value <- [1_000, 2_000] do
      Task.async(fn -> LynxIoFixture.Native.log_append(resource, value) end)
    end
    [true, true] = Enum.map(writers, &Task.await/1)
    <<123::little-16, 65_412::little-16, 65_535::little-16, 0::little-16,
      0::little-16, 65_535::little-16, tail::binary>> = File.read!("journal")
    true = tail in [
      <<1_000::little-16, 64_535::little-16, 2_000::little-16, 63_535::little-16>>,
      <<2_000::little-16, 63_535::little-16, 1_000::little-16, 64_535::little-16>>
    ]
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
