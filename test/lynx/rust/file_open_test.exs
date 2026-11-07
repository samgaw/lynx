defmodule Lynx.Rust.FileOpenTest do
  use ExUnit.Case
  alias Lynx.Rust.{FileOpenModels, Project, Proofs}

  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned patched backend")

  @tag :tmp_dir
  test "named cross-crate opens preserve distinct handles and reject stale proofs", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Open"))
    property = Path.join(project, "Open/Properties.lean")
    File.cp!(Path.join(@fixture, "OpenProperties.lean"), property)
    original = File.read!(property)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    properties =
      Enum.map(
        ~w(core_open_next distinct_handles open_error pair_first_error pair_second_error read_first_independent unsupported_path),
        &("Open.Properties." <> &1)
      )

    options = [
      roots: ["io_protocol::open_readonly", "io_protocol::open_pair", "io_core::read_once"],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      module_prefix: "Open.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Open.Properties"],
      required_properties: properties
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    audit = result.extraction.audit
    assert Enum.any?(audit.external_calls, fn {_, model} -> model[:native_file_open] end)

    assert {:ok, dependencies} =
             FileOpenModels.audit(
               audit.functions,
               audit.external_calls,
               audit.translated,
               audit.references
             )

    assert Enum.any?(dependencies, fn {_, methods} -> length(methods) == 2 end)

    # Empty enum branches can relinquish a potential file payload only after
    # checking the discriminated place against its actual local type.
    changed = Enum.map(audit.functions, &corrupt_discriminant/1)
    refute changed == audit.functions

    assert_raise CompileError, fn ->
      Lynx.Rust.NativeLifetimes.audit!(
        changed,
        audit.external_calls,
        audit.translated,
        audit.references
      )
    end

    # Losing either standard dictionary implementation must stop extraction,
    # even if the open function's type signature still looks identical.
    for {_open, methods} <- dependencies, method <- methods do
      changed =
        Map.update!(audit.translated, "fun_decls", fn functions ->
          Enum.reject(functions, &(&1 && &1["def_id"] == method))
        end)

      assert {:error, _, message} =
               FileOpenModels.audit(
                 audit.functions,
                 audit.external_calls,
                 changed,
                 audit.references
               )

      assert message =~ "concrete standard &str"
    end

    file =
      Proofs.file!(result.extraction, options[:proof_modules], required_properties: properties)

    export = Path.join(tmp, "open.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom openTrust : False",
          "private theorem unfinishedOpen : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(property, original)

    wrong = String.replace(original, "(.ok (.Ok (⟨2⟩, ⟨3⟩))", "(.ok (.Ok (⟨2⟩, ⟨2⟩))")
    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)

    source = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(source)

    changed =
      String.replace(
        rust,
        "match io_core::open_readonly(path)",
        "match io_core::open_readonly(\"other\")"
      )

    refute changed == rust
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "io-protocol", options)
      end

    assert error.message =~ "Open/Properties.lean:"
    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end

  defp corrupt_discriminant(%{"Discriminant" => %{"kind" => _} = place} = node),
    do: %{node | "Discriminant" => Map.put(place, "ty", %{"Scalar" => "Bool"})}

  defp corrupt_discriminant(node) when is_map(node),
    do: Map.new(node, fn {key, value} -> {key, corrupt_discriminant(value)} end)

  defp corrupt_discriminant(node) when is_list(node), do: Enum.map(node, &corrupt_discriminant/1)
  defp corrupt_discriminant(node), do: node
end
