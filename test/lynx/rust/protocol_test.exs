defmodule Lynx.Rust.ProtocolTest do
  use ExUnit.Case
  @unpatched System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @tools @unpatched || System.get_env("LYNX_AENEAS_DIR")
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @moduletag timeout: 900_000
  if is_nil(@tools),
    do:
      @moduletag(skip: "set LYNX_AENEAS_DIR or LYNX_UNPATCHED_AENEAS_DIR for Rust parser proofs")

  @tag tmp_dir: "process-#{System.pid()}"
  test "proves slice bounds and protocol-scale UTF-8 independently of Rustler", %{tmp_dir: tmp} do
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Protocol"))
    File.cp!(Path.join(@proofs, "Core.lean"), Path.join(project, "Protocol/Properties.lean"))
    File.cp!(Path.join(@proofs, "Utf8Cases.lean"), Path.join(project, "Protocol/Utf8Cases.lean"))
    File.cp!(Path.join(@proofs, "Utf8Scale.lean"), Path.join(project, "Protocol/Utf8Scale.lean"))
    packages(project)

    options = [
      tools: @tools,
      roots:
        Enum.map(
          ~w(parse_frame utf8_status first prefix_length),
          &("experiment_core::protocol::" <> &1)
        ),
      lean_project: project,
      module_prefix: "Protocol.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Protocol.Properties", "Protocol.Utf8Cases", "Protocol.Utf8Scale"],
      required_properties:
        Enum.map(
          ~w(first_spec first_empty split_panic split_spec utf8_valid utf8_error short wrong_version wrong_length accepted_shape parse_valid unicode_frame),
          &("Protocol.Properties." <> &1)
        ) ++ utf8_properties("Protocol")
    ]

    result = Lynx.Rust.verify!(@workspace, "experiment-core", options)
    assert [%{status: :ok}] = result.reports

    warm = Lynx.Rust.verify!(@workspace, "experiment-core", options)
    assert [%{status: :ok, cached: true}] = warm.reports

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.contains?(&1.rust_name, "from_utf8")
           )

    assert Enum.all?(
             result.verification.unverified_external_calls,
             &(&1.implementation_verified == false)
           )

    reject_mismatches(result.extraction)

    export = Path.join(tmp, "parser.export")

    file =
      Lynx.Rust.Proofs.file!(result.extraction, [
        "Protocol.Properties",
        "Protocol.Utf8Cases",
        "Protocol.Utf8Scale"
      ])

    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    model_path = Path.join(project, "Protocol/Extraction/BytesModel.lean")
    original_model = File.read!(model_path)
    File.write!(model_path, original_model <> "\nprivate axiom unexpected : False\n")
    Lynx.Rust.Project.build!(project, ["Protocol.Extraction.Funs"])
    assert [%{status: :error, cached: false}] = poisoned = Lynx.Commands.verify!(project, [file])
    assert inspect(poisoned) =~ "unexpected axiom"
    File.write!(model_path, original_model)

    scale_path = Path.join(project, "Protocol/Utf8Scale.lean")
    original_scale = File.read!(scale_path)

    wrong_offset =
      String.replace(original_scale, "offset.val = n := by", "offset.val = n + 1 := by",
        global: false
      )

    assert wrong_offset != original_scale
    File.write!(scale_path, wrong_offset)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(@workspace, "experiment-core", options)
    end

    File.write!(scale_path, original_scale)
    assert [%{status: :ok}] = Lynx.Rust.verify!(@workspace, "experiment-core", options).reports

    properties = Path.join(project, "Protocol/Properties.lean")

    File.write!(
      properties,
      String.replace(
        File.read!(properties),
        "theorem unicode_frame : protocol.parse_frame frame = .ok (.Ok 2#u64)",
        "theorem unicode_frame : protocol.parse_frame frame = .ok (.Ok 3#u64)"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(@workspace, "experiment-core", options)
    end
  end

  @tag tmp_dir: "process-#{System.pid()}"
  test "proves cross-crate parser NIFs and ordinary Elixir binary laws", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@workspace, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    native_source =
      String.replace(
        File.read!(source),
        "LynxRustFixture.BinaryNative",
        "LynxRustFixture.ProtocolNative"
      )

    native_source =
      if @unpatched do
        "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
          Regex.replace(
            ~r/(^#\[rustler::nif[^\n]*\]\n)/m,
            native_source,
            "\\1#[verify::start_from]\n"
          )
      else
        native_source
      end

    File.write!(source, native_source)

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "ProtocolNative"))
    packages(project)

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      root_attribute: if(@unpatched, do: "verify::start_from"),
      lean_project: project,
      module_prefix: "ProtocolNative.Extraction",
      build_dir: Path.join(tmp, "build"),
      cargo: [features: ["protocol"]],
      only: [parse_frame: 1, utf8_status: 1]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    core =
      File.read!(Path.join(@proofs, "Core.lean"))
      |> String.replace("Protocol.Extraction", "ProtocolNative.Extraction")
      |> String.replace(
        "open Aeneas Aeneas.Std experiment_core",
        "open Aeneas Aeneas.Std experiment_nif.experiment_core"
      )
      |> String.replace("Protocol.Properties", "ProtocolNative.Core")
      |> String.replace(
        "experiment_core.core.str.error.Utf8Error",
        "experiment_nif.core.str.error.Utf8Error"
      )
      |> then(&Regex.replace(~r/theorem first_spec.*?(?=theorem utf8_valid)/s, &1, ""))

    File.write!(Path.join(project, "ProtocolNative/Core.lean"), core)

    scale =
      File.read!(Path.join(@proofs, "Utf8Scale.lean"))
      |> String.replace("Protocol.Extraction", "ProtocolNative.Extraction")
      |> String.replace("Protocol.Utf8Scale", "ProtocolNative.Utf8Scale")
      |> String.replace(
        "experiment_core.protocol.utf8_status",
        "experiment_nif.experiment_analysis.utf8_status"
      )
      |> String.replace(
        "experiment_nif.experiment_analysis.utf8_status,",
        "experiment_nif.experiment_analysis.utf8_status, experiment_nif.experiment_core.protocol.utf8_status,"
      )

    File.write!(Path.join(project, "ProtocolNative/Utf8Scale.lean"), scale)
    parse = Enum.find(prepared.bindings.bindings, &(&1["name"] == "parse_frame"))["lean_name"]
    status = Enum.find(prepared.bindings.bindings, &(&1["name"] == "utf8_status"))["lean_name"]

    File.write!(
      Path.join(project, "ProtocolNative/Properties.lean"),
      native_properties(parse, status)
    )

    options =
      options ++
        [
          proof_modules: [
            "ProtocolNative.Core",
            "ProtocolNative.Properties",
            "ProtocolNative.Utf8Scale"
          ],
          required_properties:
            [
              "ProtocolNative.Core.wrong_version",
              "ProtocolNative.Core.wrong_length",
              "ProtocolNative.Core.accepted_shape",
              "ProtocolNative.Core.parse_valid",
              "ProtocolNative.Properties.facade_unicode",
              "ProtocolNative.Properties.facade_short"
            ] ++ utf8_properties("ProtocolNative")
        ]

    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    exports =
      for {name, arity, _} <- prepared.bindings.exports do
        args = for n <- 1..arity, do: Macro.var(String.to_atom("_arg#{n}"), nil)

        quote do
          def unquote(String.to_atom(name))(unquote_splicing(args)),
            do: :erlang.nif_error(:not_loaded)
        end
      end

    module =
      quote do
        defmodule LynxRustFixture.ProtocolNative do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(unquote(String.to_charlist(library)), 0)
          unquote_splicing(exports)
        end
      end

    elixir_source = Path.join(tmp, "native.ex")
    File.write!(elixir_source, Macro.to_string(module))

    assert {:ok, [LynxRustFixture.ProtocolNative], _} =
             Kernel.ParallelCompiler.compile_to_path([elixir_source], tmp,
               return_diagnostics: true
             )

    native = LynxRustFixture.ProtocolNative

    for {input, expected} <- [
          {<<1, 2, 195, 169>>, {:ok, 2}},
          {<<>>, {:error, 1}},
          {<<1>>, {:error, 1}},
          {<<2, 0>>, {:error, 2}},
          {<<1, 2, 65>>, {:error, 3}},
          {<<1, 1, 255>>, {:error, 4}}
        ],
        do: assert(apply(native, :parse_frame, [input]) == expected)

    for {input, expected} <- [
          {String.duplicate("😀", 262_144), {:ok, 1_048_576}},
          {:binary.copy(<<65>>, 1_048_576) <> <<255>>, {:error, {1_048_576, 1}}},
          {:binary.copy(<<65>>, 1_048_576) <> <<194>>, {:error, {1_048_576, 0}}},
          {"😀", {:ok, 4}},
          {<<255>>, {:error, {0, 1}}},
          {<<65, 194>>, {:error, {1, 0}}},
          {<<240, 144, 128, 65>>, {:error, {0, 3}}}
        ],
        do: assert(apply(native, :utf8_status, [input]) == expected)

    for input <- [5, true, <<1::size(1)>>],
        do: assert_raise(ArgumentError, fn -> apply(native, :parse_frame, [input]) end)

    [{_, beam}] = Code.compile_file(Path.join(@workspace, "elixir/protocol_laws.ex"))
    export = Path.join(tmp, "protocol.export")
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    rust = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(rust)

    for {before, after_change, diagnostic} <- [
          {"input[0] != 1", "input[0] != 2", "unsolved goals"},
          {"input.len() != length + 2", "input.len() < length + 2", "unsolved goals"},
          {"return Err(2)", "return Err(3)", "unsolved goals"},
          {"Ok(_) => Ok(input.len() as u64)", "Ok(_) => Ok(0)", "Tactic `rewrite` failed"},
          {"Some(length) => length as u8", "Some(_length) => 0", "unsolved goals"}
        ] do
      changed = String.replace(original, before, after_change)
      assert changed != original
      File.write!(rust, changed)

      error =
        assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
          Lynx.Rustler.prepare!(options)
        end

      assert Exception.message(error) =~ diagnostic
    end

    File.write!(rust, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end

  defp utf8_properties(prefix) do
    Enum.map(
      ~w(utf8_total valid_string invalid_suffix truncated_suffix megabyte_unicode megabyte_invalid megabyte_truncated),
      &(prefix <> ".Utf8Scale." <> &1)
    )
  end

  defp native_properties(parse, status) do
    """
    module
    public import ProtocolNative.Core
    public import ProtocolNative.RustlerBridge
    public section
    open Aeneas Aeneas.Std experiment_nif
    namespace ProtocolNative.Properties
    theorem composition (input : Slice U8) :
        experiment_analysis.parse_frame input = experiment_core.protocol.parse_frame input := rfl
    theorem decoded_frame : Lynx.Rustler.binaryAsSlice ⟨#[1,2,195,169]⟩ = RustM.ok ProtocolNative.Core.frame := by
      have unsigned : 4 ≤ Usize.max := by scalar_tac
      have signed : (⟨#[1,2,195,169]⟩ : ByteArray).size ≤ Isize.max.toNat := by
        change 4 ≤ Isize.max.toNat
        scalar_tac
      simp [Lynx.Rustler.binaryAsSlice, ProtocolNative.Core.frame, unsigned, signed]
      rfl
    theorem facade_unicode : #{parse} ⟨#[1,2,195,169]⟩ = RustM.ok (.Ok 2#u64) := by
      simp [#{parse}, composition, decoded_frame, ProtocolNative.Core.unicode_frame]
    theorem facade_utf8 : #{status} ⟨#[1,2,195,169]⟩ = RustM.ok (.Ok 4#u64) := by
      have valid : (ProtocolNative.Extraction.Bytes.bytes ProtocolNative.Core.frame).validateUTF8 = true := by
        decide +kernel
      obtain ⟨count, computed, size⟩ := ProtocolNative.Core.utf8_valid ProtocolNative.Core.frame valid
      have equal : count = 4#u64 := by
        apply UScalar.eq_of_val_eq
        simpa [ProtocolNative.Core.frame] using size
      simp [#{status}, experiment_analysis.utf8_status, decoded_frame, computed, equal]
    theorem facade_short (input : ByteArray) (short : input.size < 2) :
        #{parse} input = RustM.ok (.Err 1#u8) := by
      have unsigned : input.size ≤ Usize.max := by scalar_tac
      have signed : input.size ≤ Isize.max.toNat := by scalar_tac
      obtain ⟨slice, decoded, size⟩ := Lynx.Rustler.binaryAsSlice_spec input unsigned signed
      have rejected := ProtocolNative.Core.short slice (by omega)
      simp [#{parse}, composition, decoded, rejected]
    end ProtocolNative.Properties
    """
  end

  defp packages(project) do
    packages = Path.join(@workspace, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end
  end

  defp reject_mismatches(extraction) do
    audit = extraction.audit

    for model <- Map.values(audit.external_calls),
        Map.has_key?(model, :bytes_error_type) or String.contains?(model.rust_name, "split_at") or
          String.contains?(model.rust_name, "SliceIndex") do
      function = model.function

      for changed <- [
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "abi"], "C"),
            put_in(function, ["signature", "output"], %{"Scalar" => "Bool"}),
            put_in(function, ["generics", "trait_clauses"], [%{}]),
            put_in(function, ["item_meta", "name"], [%{"Ident" => ["lookalike", 0]}])
          ] do
        assert Lynx.Rust.SliceModels.resolve(changed, audit.translated, audit.references) == nil
        assert Lynx.Rust.BytesModels.resolve(changed, audit.translated, audit.references) == nil
      end
    end

    [type] =
      Enum.filter(
        audit.translated["type_decls"],
        &(&1 &&
            &1["item_meta"]["name"] ==
              Enum.map(~w(core str error Utf8Error), fn part -> %{"Ident" => [part, 0]} end))
      )

    broken =
      Map.put(
        audit.translated,
        "type_decls",
        Enum.map(audit.translated["type_decls"], fn t ->
          if t == type, do: put_in(t, ["kind", "Struct"], []), else: t
        end)
      )

    for model <- Map.values(audit.external_calls),
        Map.has_key?(model, :bytes_error_type),
        do: assert(Lynx.Rust.BytesModels.resolve(model.function, broken, audit.references) == nil)
  end
end
