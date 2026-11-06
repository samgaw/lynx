defmodule Lynx.Rustler.BinaryTest do
  use ExUnit.Case

  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "proves immutable binary preservation with an explicit FFI type model", %{tmp_dir: tmp} do
    prepared =
      Lynx.Rustler.prepare!(@fixture, "experiment-nif",
        lean_project: Path.join(@fixture, "proofs"),
        module_prefix: "RustWorkspace.BinaryFacade",
        cargo: [features: ["binary"]],
        only: [echo_binary: 1, binary_length: 1],
        proof_modules: ["RustWorkspace.Binary"],
        required_properties: [
          "RustWorkspace.Binary.core_spec",
          "RustWorkspace.Binary.composition",
          "RustWorkspace.Binary.core_length_spec",
          "RustWorkspace.Binary.length_composition",
          "RustWorkspace.Binary.length_facade_spec"
        ]
      )

    assert Enum.any?(
             prepared.verification.external_models,
             &String.contains?(&1, "unverified FFI boundary")
           )

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract &&
               evidence.theorem == "RustWorkspace.Binary.composition" &&
               "RustWorkspace.Binary.core_spec" in evidence.contracts_used
           end)

    assert [
             %{
               rust_name: "core::slice::{[@T]}::len",
               status: :modelled,
               implementation_verified: false
             },
             %{
               rust_name:
                 "rustler::types::binary::{rustler::types::binary::Binary<'a>}::as_slice",
               status: :modelled,
               implementation_verified: false
             }
           ] = prepared.verification.unverified_external_calls

    assert Enum.any?(prepared.verification.guarantees, fn evidence ->
             evidence.theorem == "RustWorkspace.Binary.length_facade_spec" and
               length(evidence.external_dependencies) == 2 and
               "RustWorkspace.Binary.length_composition" in evidence.contracts_used
           end)

    assert length(prepared.verification.unverified_nif_exports) == 10

    assert_raise ArgumentError, ~r/requires its explicit FFI type model/, fn ->
      Lynx.Rustler.Bindings.link!(
        prepared.bindings,
        Map.delete(prepared.extraction.audit, :external_types),
        prepared.extraction.translation
      )
    end

    File.mkdir_p!(Path.join(@fixture, "priv"))
    File.cp!(prepared.library, Path.join(@fixture, "priv/libexperiment_binary.so"))

    assert {:ok, [LynxRustFixture.BinaryNative], _} =
             Kernel.ParallelCompiler.compile_to_path(
               [Path.join(@fixture, "elixir/binary_native.ex")],
               tmp,
               return_diagnostics: true
             )

    for bytes <- [<<>>, <<0>>, <<0, 255, 128, 1>>, "binary", :binary.copy(<<255>>, 1024)] do
      assert apply(LynxRustFixture.BinaryNative, :echo_binary, [bytes]) == bytes
      assert apply(LynxRustFixture.BinaryNative, :binary_length, [bytes]) == byte_size(bytes)
    end

    for input <- [<<1::size(1)>>, <<1::size(9)>>, [1, 2, 3], true, 5, {1}] do
      assert_raise ArgumentError, fn ->
        apply(LynxRustFixture.BinaryNative, :echo_binary, [input])
      end
    end

    assert_raise ArgumentError, ~r/first-party type replacement/, fn ->
      Lynx.Rust.Extraction.run!(
        prepared.context,
        @tools,
        ["experiment_nif::unused"],
        tmp,
        "BinaryReplacement",
        external_types: [
          %{
            rust: "experiment_core::Reading",
            lean: "Lynx.Rustler.Binary",
            import: "RustWorkspace.RustlerBridge",
            label: "invalid"
          }
        ]
      )
    end

    [{_, beam}] = Code.compile_file(Path.join(@fixture, "elixir/binary_laws.ex"))

    reports =
      Lynx.Laws.verify([beam],
        native:
          {Lynx.Rustler,
           workspace: @fixture,
           package: "experiment-nif",
           lean_project: prepared.project,
           module_prefix: "RustWorkspace.BinaryFacade",
           cargo: [features: ["binary"]],
           only: [echo_binary: 1, binary_length: 1],
           proof_modules: ["RustWorkspace.Binary"]}
      )

    assert Enum.all?(reports, &(&1.status == :ok)),
           inspect(reports, pretty: true, limit: :infinity)

    assert Enum.any?(reports, fn report ->
             Enum.any?(
               Map.get(report, :external_models, []),
               &String.contains?(&1, "unverified FFI boundary")
             )
           end)

    warm =
      Lynx.Laws.verify([beam], externals: [prepared.external], lean_project: prepared.project)

    assert Enum.all?(warm, &(&1.status == :ok && &1.cached))
    export = Path.join(tmp, "binary.export")

    checked =
      Lynx.Laws.verify([beam],
        externals: [prepared.external],
        lean_project: prepared.project,
        export: export
      )

    assert Enum.all?(checked, &(&1.status == :ok)), inspect(checked, limit: :infinity)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

    {status, output} =
      Lynx.Commands.lake(prepared.project, ["check", "--from-export", export] ++ sandbox)

    assert status == 0, output

    assert_raise CompileError, ~r/unverified external Rust call/, fn ->
      Lynx.Rustler.prepare!(@fixture, "experiment-nif",
        lean_project: prepared.project,
        module_prefix: "RustWorkspace.BinaryFacade",
        cargo: [features: ["unsupported-binary-method"]],
        only: [binary_owned_length: 1]
      )
    end
  end
end
