defmodule Lynx.Rustler.VectorResourceTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_BUFFER_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_NATIVE_BUFFER_DIR for owned vector resource proofs")

  @tag :tmp_dir
  test "verifies owned vector resources through compiled Rustler calls", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxAtomicFixture", "LynxVectorBufferFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Buffer"))
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
      root_attribute: "lynx::buffer_copy",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Buffer.Extraction",
      only: [buffer_new: 2, buffer_copy: 1, buffer_length: 1, buffer_head: 1]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    properties =
      Enum.reduce(
        [{"buffer_new", "__NEW__"}, {"buffer_length", "__LENGTH__"}, {"buffer_head", "__HEAD__"}],
        File.read!(Path.join(@fixture, "BufferProperties.lean")),
        fn {name, placeholder}, source ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(source, placeholder, binding["lean_name"])
        end
      )

    property = Path.join(project, "Buffer/Properties.lean")
    File.write!(property, properties)

    [copy_binding] = Enum.filter(prepared.bindings.bindings, &(&1["name"] == "buffer_copy"))

    copy_properties =
      File.read!(Path.join(@fixture, "BufferCopyProperties.lean"))
      |> String.replace("__COPY__", copy_binding["lean_name"])

    File.write!(Path.join(project, "Buffer/CopyProperties.lean"), copy_properties)

    options =
      common ++
        [
          proof_modules: ["Buffer.Properties", "Buffer.CopyProperties"],
          required_properties:
            Enum.map(
              ~w(core_length length_composition core_head head_composition cleanup dispose create read_length read_head final_release),
              &("Buffer.Properties." <> &1)
            ) ++
              Enum.map(
                ~w(append_eq append_preserves_prefix copy_bytes_eq facade_view facade_bytes),
                &("Buffer.CopyProperties." <> &1)
              )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{lean_name: "atomic_nif.ByteBuffer.drop_owned"}] =
             prepared.verification.resource_cleanup

    assert Enum.any?(
             prepared.verification.structural_drops,
             &match?(
               %{type: "alloc::vec::Vec<u8>", status: :modelled, implementation_verified: false},
               &1
             )
           )

    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    audit = prepared.extraction.audit

    type =
      Enum.find(
        audit.translated["type_decls"],
        &(&1 &&
            &1["item_meta"]["name"] == [
              %{"Ident" => ["atomic_nif", 0]},
              %{"Ident" => ["ByteBuffer", 0]}
            ])
      )

    assert %{"needs_drop" => true} = type

    payload = %{
      "Adt" => %{
        "id" => type["def_id"],
        "builtin" => nil,
        "generics" => Lynx.Rust.ResourceModels.args([])
      }
    }

    helper = Lynx.Rust.NativeOwnedDrops.function_for(payload, audit.translated, audit.references)
    assert helper != nil

    changed =
      update_in(audit.translated, ["fun_decls"], fn functions ->
        Enum.map(functions, fn function ->
          if function && function["def_id"] == helper["def_id"] do
            update_in(function, ["body", "Structured", "body", "statements"], fn statements ->
              Enum.map(statements, fn statement ->
                case statement["kind"] do
                  %{"Drop" => _} ->
                    put_in(
                      statement,
                      ["kind", "Drop", "fn_ptr", "generics", "types", Access.at(1)],
                      %{"Scalar" => "Bool"}
                    )

                  _ ->
                    statement
                end
              end)
            end)
          else
            function
          end
        end)
      end)

    assert Lynx.Rust.NativeOwnedDrops.function_for(payload, changed, audit.references) == nil
    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxVectorBufferFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    native = LynxVectorBufferFixture.Native

    for {first, second, expected} <- [{5, 9, 5}, {9, 5, 9}, {0, 255, 0}, {261, 9, 5}] do
      handle = apply(native, :buffer_new, [first, second])
      assert apply(native, :buffer_length, [handle]) == 2
      assert apply(native, :buffer_head, [handle]) == expected
      assert apply(native, :buffer_length, [handle]) == 2
    end

    for args <- [[false, 9], [-1, 9], [5, 4_294_967_296]],
        do: assert_raise(ArgumentError, fn -> apply(native, :buffer_new, args) end)

    for value <- [0, false, apply(native, :atomic_new, [1])],
        do: assert_raise(ArgumentError, fn -> apply(native, :buffer_length, [value]) end)

    # Runtime calibration supplements the implementation-linked Rust contracts
    # and the closed beyond_4k Elixir law below.
    large = apply(native, :buffer_copy, [:binary.copy(<<17>>, 4097)])
    assert apply(native, :buffer_length, [large]) == 4097
    assert apply(native, :buffer_head, [large]) == 17

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/buffer_laws.ex"))

    for law <-
          ~w(observes reverse_order reuses_vm_owner narrows_byte invalid_first negative_first invalid_second invalid_resource)a,
        do: assert(apply(law_module, law, []))

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 32768, maxHeartbeats: 24_000_000]
    ]

    [{copy_law_module, copy_beam}] =
      Code.compile_file(Path.join(workspace, "elixir/buffer_copy_laws.ex"))

    for law <- ~w(copies empty raw_bytes independent_buffers rejects_list rejects_bits beyond_4k)a,
        do: assert(apply(copy_law_module, law, []))

    export = Path.join(tmp, "buffer-laws.export")
    reports = Lynx.Laws.verify([beam, copy_beam], Keyword.put(law_options, :export, export))
    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 15
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Buffer.Properties", "Buffer.CopyProperties"],
        module: "Buffer.ExportAudit"
      )

    native_export = Path.join(tmp, "buffer-native.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: native_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", native_export] ++ sandbox)

    assert status == 0, output

    assert Enum.all?(
             Lynx.Laws.verify([beam, copy_beam], law_options),
             &(&1.status == :ok and &1.cached)
           )

    laws = File.read!(Path.join(workspace, "elixir/buffer_laws.ex"))

    [{_, incorrect}] =
      laws
      |> String.replace("LynxVectorBufferFixture.Laws", "LynxVectorBufferFixture.FalseLaws")
      |> String.replace("buffer_head(buffer) == 5", "buffer_head(buffer) == 6")
      |> Code.compile_string("buffer_false_laws.ex")

    assert Enum.any?(Lynx.Laws.verify([incorrect], law_options), &(&1.status == :error))

    for invalid <- [
          "private axiom uncheckedBuffer : False",
          "private theorem unfinishedBuffer : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, properties)
    original = File.read!(source)
    altered = String.replace(original, "bytes.push(second);", "bytes.push(first);")
    assert altered != original
    File.write!(source, altered)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

    core_source = Path.join(workspace, "core/src/lib.rs")
    core_original = File.read!(core_source)

    core_changed =
      String.replace(
        core_original,
        "output.extend_from_slice(input);",
        "output.extend_from_slice(input);\n    output.extend_from_slice(input);"
      )

    assert core_changed != core_original
    File.write!(core_source, core_changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core_source, core_original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

    File.write!(
      source,
      original <>
        "\nimpl Drop for ByteBuffer { fn drop(&mut self) { panic!(\"observable buffer drop\"); } }\n"
    )

    assert_raise CompileError, ~r/resource|drop|destruct/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
