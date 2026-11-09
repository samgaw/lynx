defmodule Lynx.Rustler.ListBoundaryTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_PURE_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_PURE_AENEAS_DIR or LYNX_AENEAS_DIR")

  @tag :tmp_dir
  test "kernel checks list composition and rejects the old overflowing allocation domain", %{
    tmp_dir: tmp
  } do
    project = Path.join(tmp, "proofs")
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    Lynx.Rust.Project.ensure!(project, "ListBoundary", @tools)
    module = Lynx.Rustler.Bridge.install!(project, "ListBoundary.Extraction")
    Lynx.Rust.Project.build!(project, [module])

    file = %{
      "module" => "ListBoundary.Audit",
      "file" => "ListBoundary.Audit.lean",
      "imports" => [module],
      "contents" => [],
      "audit_modules" => [module],
      "preludes" => []
    }

    export = Path.join(project, "boundary.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    path = Path.join(project, "ListBoundary/RustlerBridge.lean")
    original = File.read!(path)

    for extra <- [
          "private axiom listTrust : False",
          "private theorem unfinishedList : True := by sorry"
        ] do
      File.write!(path, original <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, [module])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    overflowing =
      String.replace(
        original,
        "if value.val.length ≤ 2147483647 then",
        "if value.val.length ≤ 4294967295 then"
      )

    refute overflowing == original
    File.write!(path, overflowing)

    assert_raise RuntimeError, ~r/unsolved goals/, fn ->
      Lynx.Rust.Project.build!(project, [module])
    end

    File.write!(path, original)
    Lynx.Rust.Project.build!(project, [module])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file])
  end
end
