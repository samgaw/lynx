defmodule Lynx.Rust.BorrowedConstantsTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/BorrowedConstants.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for static slice proofs")

  @tag :tmp_dir
  test "proves borrowed constant bytes and parsing across workspace crates", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "BorrowedConstants"))
    File.cp!(@proof, Path.join(project, "BorrowedConstants/Properties.lean"))
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      tools: @tools,
      roots: ["experiment_analysis::borrowed_magic_word", "experiment_analysis::binary_tag_bytes"],
      lean_project: project,
      module_prefix: "BorrowedConstants.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["BorrowedConstants.Properties"],
      required_properties:
        Enum.map(
          ~w(marker_bytes binary_bytes core_word caller_word caller_binary),
          &("BorrowedConstants.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports

    for name <- ["BORROWED_MAGIC", "BINARY_TAG"],
        do:
          assert(
            Enum.any?(
              result.verification.constants,
              &(&1["status"] == :extracted and String.ends_with?(&1["lean_name"], "." <> name))
            )
          )

    assert Enum.all?(
             result.verification.unverified_external_calls,
             &(&1.implementation_verified == false)
           )

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    export = Path.join(tmp, "borrowed-constants.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["BorrowedConstants.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)

    for {before, replacement} <- [
          {~s(BORROWED_MAGIC: &[u8] = b"LYNX"), ~s(BORROWED_MAGIC: &[u8] = b"LYNY")},
          {~s(BORROWED_MAGIC: &[u8] = b"LYNX"), ~s(BORROWED_MAGIC: &[u8] = b"LYN")},
          {~S(BINARY_TAG: &[u8] = b"L\0\xff"), ~S(BINARY_TAG: &[u8] = b"L\0\xfe")},
          {"u32::from_be_bytes([input[0], input[1], input[2], input[3]])",
           "u32::from_le_bytes([input[0], input[1], input[2], input[3]])"}
        ] do
      changed = String.replace(original, before, replacement)
      assert changed != original
      File.write!(source, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end
    end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports
  end
end
