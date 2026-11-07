defmodule Lynx.Rustler.VecTest do
  use ExUnit.Case

  @tools System.get_env("LYNX_AENEAS_DIR")
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_collections", __DIR__)
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for byte-vector NIF proofs")

  @tag tmp_dir: "process-#{System.pid()}"
  test "Rustler 0.39 byte-vector decoding and mutation compose into Elixir laws", %{tmp_dir: tmp} do
    verify_version("0.39.0", tmp)
  end

  @tag tmp_dir: "process-#{System.pid()}"
  test "Rustler 0.38 uses the same checked byte-vector boundary", %{tmp_dir: tmp} do
    verify_version("0.38.0", tmp)
  end

  defp verify_version(version, tmp) do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@workspace, entry), Path.join(workspace, entry))

    suffix = if version == "0.39.0", do: "39", else: "38"
    native = Module.concat(LynxRustFixture, "ByteVec#{suffix}Native")
    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(
        File.read!(source),
        "LynxRustFixture.Native",
        "LynxRustFixture.ByteVec#{suffix}Native"
      )
    )

    if version == "0.38.0" do
      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=0.38.0"))

      {output, status} =
        System.cmd(
          "cargo",
          [
            "update",
            "--manifest-path",
            Path.join(workspace, "Cargo.toml"),
            "-p",
            "rustler",
            "--precise",
            version
          ],
          stderr_to_stdout: true
        )

      assert status == 0, output
    end

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "ByteVecNative"))
    packages = Path.join(@workspace, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "ByteVecNative.Extraction",
      cargo: [features: ["collections"]],
      only: [replace_first: 2]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "arguments" => [%{"vec" => "u8"}, "u8"],
               "result" => %{"tuple" => ["bool", %{"vec" => "u8"}]}
             } = binding
           ] = prepared.bindings.bindings

    assert prepared.verification.rustler_version == version

    assert Enum.any?(
             prepared.verification.external_models,
             &String.contains?(&1, "1048576-element")
           )

    reject_shadow_type(prepared)
    properties(project, binding["lean_name"])

    options =
      options ++
        [
          proof_modules: ["ByteVecNative.Core", "ByteVecNative.Properties"],
          required_properties: [
            "ByteVecNative.Core.vector_transition",
            "ByteVecNative.Core.composition",
            "ByteVecNative.Properties.facade",
            "ByteVecNative.Properties.facade_empty"
          ]
        ]

    load_native(prepared, native, tmp)

    for {input, expected} <- [
          {[], {false, []}},
          {[1, 2, 3], {true, [9, 2, 3]}},
          {[256, 4_294_967_295], {true, [9, 255]}}
        ] do
      assert apply(native, :replace_first, [input, 9]) == expected
    end

    assert apply(native, :replace_first, [[1], 256]) == {true, [0]}

    for input <- [false, <<1>>, 5, [-1], [4_294_967_296], [false | 2], [1, false | 2]] do
      assert_raise ArgumentError, fn -> apply(native, :replace_first, [input, 9]) end
    end

    assert catch_error(apply(native, :replace_first, [[1 | 2], 9])) == :nif_panicked
    assert catch_error(apply(native, :replace_first, [[1 | 2], false])) == :nif_panicked

    laws_source = Path.join(tmp, "laws.ex")
    File.write!(laws_source, laws(native, suffix))
    [{_, beam}] = Code.compile_file(laws_source)
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})
    assert_verified(reports)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    if version == "0.39.0" do
      warm = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})
      assert Enum.all?(warm, &(&1.status == :ok && &1.cached)), inspect(warm, limit: :infinity)
      export = Path.join(tmp, "bytevec.export")
      checked = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
      assert_verified(checked)
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output
      source = Path.join(workspace, "core/src/collections.rs")
      original = File.read!(source)
      changed = String.replace(original, "input[0] = value;", "input[0] = 0;")
      assert changed != original
      File.write!(source, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end
  end

  defp assert_verified(reports) do
    errors =
      for report <- reports, report.status != :ok do
        %{
          module: report.module,
          diagnostics: Enum.filter(report.diagnostics, &(&1.severity == :error))
        }
      end

    assert errors == [], inspect(errors, limit: :infinity)
  end

  defp properties(project, facade) do
    core =
      File.read!(Path.join(@proofs, "Properties.lean"))
      |> String.split("theorem shared_core", parts: 2)
      |> hd()

    core =
      (core <> "\nend Collections.Properties\n")
      |> String.replace("Collections.Extraction", "ByteVecNative.Extraction")
      |> String.replace("Collections.Properties", "ByteVecNative.Core")
      |> String.replace(
        "open Aeneas Aeneas.Std experiment_analysis",
        "open Aeneas Aeneas.Std experiment_nif"
      )
      |> then(
        &Regex.replace(
          ~r/(?<![\w.])replace_first(?= input value)/,
          &1,
          "experiment_analysis.replace_first"
        )
      )

    File.write!(Path.join(project, "ByteVecNative/Core.lean"), core)

    File.write!(
      Path.join(project, "ByteVecNative/Properties.lean"),
      File.read!(Path.join(@proofs, "Native.lean")) |> String.replace("__FACADE__", facade)
    )
  end

  defp reject_shadow_type(prepared) do
    audit = prepared.extraction.audit

    index =
      Enum.find_index(
        audit.translated["type_decls"],
        &(&1 &&
            &1["item_meta"]["name"] ==
              Enum.map(~w(alloc vec Vec), fn part -> %{"Ident" => [part, 0]} end))
      )

    changed =
      put_in(audit, [:translated, "type_decls", Access.at(index), "item_meta", "name"], [
        %{"Ident" => ["FakeVec", 0]}
      ])

    assert_raise ArgumentError, ~r/unsupported NIF ADT identity/, fn ->
      Lynx.Rustler.Bindings.link!(prepared.bindings, changed, prepared.extraction.translation)
    end
  end

  defp load_native(prepared, native, tmp) do
    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    exports =
      for {name, arity, _} <- prepared.bindings.exports do
        args = for index <- 1..arity, do: Macro.var(String.to_atom("_arg#{index}"), nil)

        quote do
          def unquote(String.to_atom(name))(unquote_splicing(args)),
            do: :erlang.nif_error(:not_loaded)
        end
      end

    ast =
      quote do
        defmodule unquote(native) do
          @compile :debug_info
          @on_load :load_nif
          def load_nif, do: :erlang.load_nif(unquote(String.to_charlist(library)), 0)
          unquote_splicing(exports)
        end
      end

    path = Path.join(tmp, "native.ex")
    File.write!(path, Macro.to_string(ast))

    assert {:ok, [^native], _} =
             Lynx.Rustler.NifFixture.compile!(path, tmp, native)
  end

  defp laws(native, suffix) do
    ~s'''
    defmodule LynxRustFixture.ByteVec#{suffix}Laws do
      @compile :debug_info
      use Lynx.Laws
      law replaces_first,
        expects: #{inspect(native)}.replace_first([1,2,3], 9) == {true, [9,2,3]},
        proof: ~LEAN"""
        simp only [«replaces_first:ensures/0», Elixir.#{inspect(native)}.«replace_first/2»,
          Elixir.#{inspect(native)}.«replace_first:execution/2»]
        rw [ByteVecNative.Properties.decode_sample]
        have decoded : Lynx.Rustler.decodeUnsigned .U8 32 (.integer 9) = .ok 9#u8 := by
          simp [Lynx.Rustler.decodeUnsigned]; rfl
        simp [decoded, ByteVecNative.Properties.facade_sample, ByteVecNative.Properties.encode_sample,
          Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
        """
      law empty_unchanged(value),
        requires: is_integer(value) and value >= 0 and value < 4294967296,
        expects: #{inspect(native)}.replace_first([], value) == {false, []},
        proof: ~LEAN"""
        cases value <;> simp [«empty_unchanged:requires/1», Erlang.erlang.«is_integer/1»] at requires
        rename_i number
        simp [«empty_unchanged:ensures/1», Elixir.#{inspect(native)}.«replace_first/2»,
          Elixir.#{inspect(native)}.«replace_first:execution/2», ByteVecNative.Properties.decode_empty,
          ByteVecNative.Properties.facade_empty, ByteVecNative.Properties.encode_empty,
          Lynx.Rustler.decodeUnsigned, requires.1, requires.2, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
        """
      law narrows_elements,
        expects: #{inspect(native)}.replace_first([256, 4294967295], 9) == {true, [9, 255]},
        proof: ~LEAN"""
        simp only [«narrows_elements:ensures/0», Elixir.#{inspect(native)}.«replace_first/2»,
          Elixir.#{inspect(native)}.«replace_first:execution/2»]
        rw [ByteVecNative.Properties.decode_narrow]
        have decoded : Lynx.Rustler.decodeUnsigned .U8 32 (.integer 9) = .ok 9#u8 := by
          simp [Lynx.Rustler.decodeUnsigned]; rfl
        simp [decoded, ByteVecNative.Properties.facade_narrow, ByteVecNative.Properties.encode_narrow,
          Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
        """
      law improper_panics,
        expects: (try do
          #{inspect(native)}.replace_first([1 | 2], 9) == :nif_panicked
        catch :error, :nif_panicked -> true end),
        proof: ~LEAN"""
        have rejected := Lynx.Rustler.decodeByteVec_improper 1#u8 2
        simp [Lynx.Rustler.encodeUnsigned] at rejected
        simp [«improper_panics:ensures/0», Elixir.#{inspect(native)}.«replace_first/2», rejected,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        """
      law bad_element_precedes_tail,
        expects: (try do
          #{inspect(native)}.replace_first([false | 2], 9) == :badarg
        catch :error, :badarg -> true end),
        proof: ~LEAN"""
        have rejected := Lynx.Rustler.decodeByteVec_headError (.atom "false") (.integer 2)
          (.error (.atom "badarg")) (by simp [Lynx.Rustler.decodeUnsigned])
        simp [«bad_element_precedes_tail:ensures/0», Elixir.#{inspect(native)}.«replace_first/2», rejected,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        """
    end
    '''
  end
end
