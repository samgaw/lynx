defmodule Lynx.Rust.OverflowTest do
  use ExUnit.Case
  @fixture Path.expand("../fixtures/rust_workspace", __DIR__)
  @proofs Path.join(@fixture, "proofs")
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "preserves wrapping arithmetic from a release Cargo build", %{tmp_dir: tmp} do
    prefix = "RustWorkspace.OverflowC#{Base.encode16(:crypto.strong_rand_bytes(8), case: :lower)}"

    on_exit(fn ->
      File.rm_rf!(Path.join(@proofs, String.replace(prefix, ".", "/")))

      for suffix <- [".llbc", ".translation.json"],
          do: File.rm(Path.join(@proofs, String.replace(prefix, ".", "_") <> suffix))
    end)

    context =
      Lynx.Rust.Cargo.build!(@fixture, "experiment-analysis", Path.join(tmp, "build"),
        profile: "release"
      )

    extraction =
      Lynx.Rust.Extraction.run!(
        context,
        @tools,
        ["experiment_analysis::twice_plus_one"],
        @proofs,
        prefix
      )

    assert %{"overflow_checks" => false} = extraction.audit.translated["runtime_checks"]

    {output, status} =
      System.cmd("lake", ["build", prefix <> ".Funs"], cd: @proofs, stderr_to_stdout: true)

    assert status == 0, output

    source = """
    module
    public import #{prefix}.Funs
    open Aeneas Aeneas.Std
    theorem wrapping_result : experiment_analysis.twice_plus_one 4611686018427387904#i64 =
        RustM.ok (I64.ofInt (-9223372036854775807)) := by
      simp [experiment_analysis.twice_plus_one, experiment_analysis.experiment_core.double, bind_ok]
      decide
    """

    file = %{
      "module" => prefix <> ".Property",
      "file" => "wrapping-property.lean",
      "imports" => [prefix <> ".Funs"],
      "contents" => [],
      "preludes" => [
        %{
          "source" => source,
          "file" => "wrapping-property.lean",
          "span" => [1],
          "indentation" => 0
        }
      ],
      "audit_modules" => [prefix <> ".Funs", prefix <> ".Property"]
    }

    [report] = Lynx.Commands.verify!(@proofs, [file])
    assert report.status == :ok, inspect(report, pretty: true, limit: :infinity)
  end
end
