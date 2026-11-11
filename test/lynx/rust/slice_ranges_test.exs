defmodule Lynx.Rust.SliceRangesTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/Slices.lean", __DIR__)
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for Rust slice range proofs")

  @tag :tmp_dir
  test "composes windows, remainders and exact parser consumption", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    for crate <- ~w(base analysis), do: File.mkdir_p!(Path.join([workspace, crate, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["base", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "base/Cargo.toml"), """
    [package]
    name = "slice-base"
    version = "0.1.0"
    edition = "2021"
    """)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "slice-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    slice-base = { path = "../base" }
    """)

    base = Path.join(workspace, "base/src/lib.rs")

    base_source = """
    /// Borrows a window, rejecting reversed or out-of-bounds endpoints.
    pub fn window(input: &[u8], start: usize, end: usize) -> Option<&[u8]> {
        input.get(start..end)
    }
    /// Borrows the unconsumed bytes after a validated position.
    pub fn remainder(input: &[u8], start: usize) -> Option<&[u8]> {
        input.get(start..)
    }
    """

    File.write!(base, base_source)
    caller = Path.join(workspace, "analysis/src/lib.rs")

    caller_source = """
    /// Composes a borrowed window across a workspace dependency.
    pub fn window(input: &[u8], start: usize, end: usize) -> Option<&[u8]> {
        slice_base::window(input, start, end)
    }
    /// Composes a borrowed remainder across a workspace dependency.
    pub fn remainder(input: &[u8], start: usize) -> Option<&[u8]> {
        slice_base::remainder(input, start)
    }
    /// Separates a bounded payload and its exact unconsumed remainder.
    pub fn split(input: &[u8], end: usize) -> Option<(&[u8], &[u8])> {
        let payload = slice_base::window(input, 0, end)?;
        let rest = slice_base::remainder(input, end)?;
        Some((payload, rest))
    }
    """

    File.write!(caller, caller_source)

    {output, status} =
      System.cmd(
        "cargo",
        ["generate-lockfile", "--manifest-path", Path.join(workspace, "Cargo.toml")],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Window"))
    proof = Path.join(project, "Window/Properties.lean")
    File.cp!(@proof, proof)
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["slice_analysis::window", "slice_analysis::remainder", "slice_analysis::split"],
      lean_project: project,
      module_prefix: "Window.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Window.Properties"],
      required_properties:
        Enum.map(
          ~w(core_window core_remainder window_bytes remainder_bytes split_bytes exact_consumption consumption_sizes),
          &("Window.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "slice-analysis", options)
    assert Enum.all?(result.reports, &(&1.status == :ok))

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract and
                 &1.theorem == "Window.Properties.exact_consumption")
           )

    for range <- ["Range", "RangeFrom"] do
      assert Enum.any?(result.verification.unverified_external_calls, fn model ->
               model.rust_name ==
                 "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::#{range}<usize>, [@T], [@T]>}::get" and
                 model.status == :modelled and model.implementation_verified == false
             end)
    end

    warm = Lynx.Rust.verify!(workspace, "slice-analysis", options)
    assert Enum.all?(warm.reports, &(&1.status == :ok and &1.cached))

    file =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "slices.export")
    assert Enum.all?(Lynx.Commands.verify!(project, [file], export: export), &(&1.status == :ok))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    document = JSON.decode!(File.read!(result.extraction.llbc))

    for {id, model} <- result.extraction.audit.external_calls,
        String.contains?(model.lean, "SliceIndexRange") do
      invalid =
        update_in(document, ["translated", "fun_decls"], fn functions ->
          Enum.map(functions, fn
            %{"def_id" => ^id} = function ->
              put_in(function, ["signature", "output"], %{"Scalar" => "Bool"})

            function ->
              function
          end)
        end)

      assert_raise CompileError, ~r/unsupported SliceIndex/, fn ->
        Lynx.Rust.LLBC.audit!(invalid, ["slice_base", "slice_analysis"])
      end
    end

    for {source, original, changed} <- [
          {base, base_source,
           String.replace(base_source, "input.get(start..end)", "input.get(..end)")},
          {base, base_source,
           String.replace(base_source, "input.get(start..)", "input.get(..start)")},
          {caller, caller_source,
           String.replace(
             caller_source,
             "slice_base::remainder(input, end)",
             "slice_base::remainder(input, 0)"
           )}
        ] do
      refute changed == original
      File.write!(source, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "slice-analysis", options)
      end

      File.write!(source, original)
    end

    restored = Lynx.Rust.verify!(workspace, "slice-analysis", options)
    assert Enum.all?(restored.reports, &(&1.status == :ok))
  end
end
