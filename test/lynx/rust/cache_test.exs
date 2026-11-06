defmodule Lynx.Rust.CacheTest do
  use ExUnit.Case

  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.join(@fixture, "proofs")
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "changed first-party implementation invalidates dependants but preserves unrelated proofs",
       %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for file <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated) do
      File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))
    end

    prefix = "RustWorkspace.CacheC#{Base.encode16(:crypto.strong_rand_bytes(8), case: :lower)}"

    on_exit(fn ->
      File.rm_rf!(Path.join(@proofs, String.replace(prefix, ".", "/")))

      for path <- Path.wildcard(Path.join(@proofs, String.replace(prefix, ".", "_") <> "*")),
          do: File.rm(path)
    end)

    analysis =
      extract!(
        workspace,
        "experiment-analysis",
        "experiment_analysis::restore",
        prefix <> ".Analysis",
        tmp
      )

    unrelated =
      extract!(
        workspace,
        "experiment-unrelated",
        "experiment_unrelated::identity",
        prefix <> ".Unrelated",
        tmp
      )

    files = [property(analysis, :analysis), property(unrelated, :unrelated)]

    assert [%{status: :ok, cached: false}, %{status: :ok, cached: false}] =
             Lynx.Commands.verify!(@proofs, files)

    assert [%{status: :ok, cached: true}, %{status: :ok, cached: true}] =
             Lynx.Commands.verify!(@proofs, files)

    source = Path.join(workspace, "core/src/lib.rs")
    File.write!(source, String.replace(File.read!(source), "    !value", "    value && false"))

    changed =
      extract!(
        workspace,
        "experiment-analysis",
        "experiment_analysis::restore",
        prefix <> ".Analysis",
        tmp
      )

    independent =
      extract!(
        workspace,
        "experiment-unrelated",
        "experiment_unrelated::identity",
        prefix <> ".Unrelated",
        tmp
      )

    refute changed.fingerprint == analysis.fingerprint
    assert independent.fingerprint == unrelated.fingerprint

    assert [%{status: :error, cached: false}, %{status: :ok, cached: true}] =
             Lynx.Commands.verify!(@proofs, [
               property(changed, :analysis),
               property(independent, :unrelated)
             ])

    # Even a stale client source key cannot hide replacement imported artifacts.
    [stale, unaffected] = files

    assert [%{status: :error, cached: false}, %{status: :ok, cached: true}] =
             Lynx.Commands.verify!(@proofs, [stale, unaffected])
  end

  defp extract!(workspace, package, root, prefix, tmp) do
    context = Lynx.Rust.Cargo.build!(workspace, package, Path.join([tmp, "build", package]))
    extraction = Lynx.Rust.Extraction.run!(context, @tools, [root], @proofs, prefix)

    {output, status} =
      System.cmd("lake", ["build", prefix <> ".Funs"], cd: @proofs, stderr_to_stdout: true)

    assert status == 0, output
    extraction
  end

  defp property(extraction, kind) do
    proof =
      case kind do
        :analysis ->
          """
          theorem composition (value : Bool) : experiment_analysis.restore value = RustM.ok value := by
            cases value <;> simp [experiment_analysis.restore, experiment_analysis.experiment_core.invert, bind_ok]
          """

        :unrelated ->
          """
          theorem identity (value : I64) : experiment_unrelated.identity value = RustM.ok value := by rfl
          """
      end

    module = extraction.module <> ".Property"
    source = "module\npublic import #{extraction.module}.Funs\nopen Aeneas Aeneas.Std\n" <> proof

    %{
      "module" => module,
      "file" => module <> ".lean",
      "imports" => [extraction.module <> ".Funs"],
      "contents" => [],
      "cache_key" => Lynx.Rust.Fingerprint.digest(source <> extraction.fingerprint),
      "preludes" => [
        %{"source" => source, "file" => module <> ".lean", "span" => [1], "indentation" => 0}
      ],
      "audit_modules" => [module, extraction.module <> ".Funs"]
    }
  end
end
