defmodule Lynx.Rust.BorrowedPrefixTest do
  use ExUnit.Case

  @tools System.get_env("LYNX_AENEAS_DIR")
  @packages Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "borrowed prefixes preserve exact contents and bounds across crates", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    for crate <- ~w(core analysis), do: File.mkdir_p!(Path.join([workspace, crate, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["core", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "core/Cargo.toml"), """
    [package]
    name = "prefix-core"
    version = "0.1.0"
    edition = "2021"
    """)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "prefix-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    prefix-core = { path = "../core" }
    """)

    source = Path.join(workspace, "core/src/lib.rs")

    original = """
    pub fn prefix(input: &[u8], length: Option<usize>) -> Option<&[u8]> {
        match length {
            Some(length) => input.get(..length),
            None => None,
        }
    }
    """

    File.write!(source, original)

    File.write!(Path.join(workspace, "analysis/src/lib.rs"), """
    pub fn prefix(input: &[u8], length: Option<usize>) -> Option<&[u8]> {
        prefix_core::prefix(input, length)
    }
    """)

    {output, status} =
      System.cmd(
        "cargo",
        ["generate-lockfile", "--manifest-path", Path.join(workspace, "Cargo.toml")],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Prefix"))

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "Prefix/Properties.lean"), """
    module
    public import Prefix.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace Prefix.Properties
     theorem payload (input : Slice U8) (length : Option Usize) :
        (do let output ← prefix_analysis.prefix_core.prefix input length; pure (output.map Slice.val)) =
          RustM.ok (length.bind fun n => if n.val ≤ input.val.length then some (input.val.take n.val) else none) := by
      cases length with
      | none => simp [prefix_analysis.prefix_core.prefix, pure]
      | some n =>
        simp only [prefix_analysis.prefix_core.prefix, core.slice.Slice.get,
          core.slice.index.SliceIndexRangeToUsizeSlice.get]
        split <;> simp_all [Slice.length, List.slice, pure]

     theorem composed (input : Slice U8) (length : Option Usize) :
        (do let output ← prefix_analysis.prefix input length; pure (output.map Slice.val)) =
          RustM.ok (length.bind fun n => if n.val ≤ input.val.length then some (input.val.take n.val) else none) := by
      exact payload input length
    end Prefix.Properties
    """)

    options = [
      roots: ["prefix_analysis::prefix"],
      lean_project: project,
      module_prefix: "Prefix.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Prefix.Properties"],
      required_properties: ["Prefix.Properties.payload", "Prefix.Properties.composed"]
    ]

    result = Lynx.Rust.verify!(workspace, "prefix-analysis", options)
    assert Enum.all?(result.reports, &(&1.status == :ok))

    assert Enum.any?(result.verification.unverified_external_calls, fn
             %{
               rust_name:
                 "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get",
               status: :modelled,
               implementation_verified: false
             } ->
               true

             _ ->
               false
           end)

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))
    warm = Lynx.Rust.verify!(workspace, "prefix-analysis", options)
    assert Enum.all?(warm.reports, &(&1.status == :ok and &1.cached))

    proof =
      Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    files =
      Lynx.Translation.new(
        externals: [
          %Lynx.External{bindings: [], files: [proof], fingerprint: result.extraction.fingerprint}
        ]
      )
      |> Lynx.Translation.assemble()

    export = Path.join(tmp, "prefix.export")
    assert Enum.all?(Lynx.Commands.verify!(project, files, export: export), &(&1.status == :ok))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    document = JSON.decode!(File.read!(result.extraction.llbc))

    model =
      Enum.find_value(result.extraction.audit.external_calls, fn
        {_, %{lean: "Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.get"} = model} ->
          model

        _ ->
          nil
      end)

    assert model
    impl_id = model.function["src"]["TraitImpl"]["impl_ref"]["id"]

    for change <- [
          &Map.put(&1, "methods", []),
          &Map.put(&1, "is_negative", true),
          &put_in(&1, ["impl_trait", "generics", "types"], [])
        ] do
      invalid =
        update_in(document, ["translated", "trait_impls"], fn impls ->
          Enum.map(impls, fn
            %{"def_id" => ^impl_id} = impl -> change.(impl)
            impl -> impl
          end)
        end)

      assert_raise CompileError, ~r/unsupported SliceIndex/, fn ->
        Lynx.Rust.LLBC.audit!(invalid, ["prefix_core", "prefix_analysis"])
      end
    end

    # Changing the implementation must invalidate the proof, including the
    # dependent caller, rather than reuse the previous successful extraction.
    File.write!(source, String.replace(original, "input.get(..length)", "input.get(..0)"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "prefix-analysis", options)
    end

    File.write!(source, original)
    restored = Lynx.Rust.verify!(workspace, "prefix-analysis", options)
    assert Enum.all?(restored.reports, &(&1.status == :ok))
  end
end
