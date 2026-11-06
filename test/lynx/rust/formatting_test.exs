defmodule Lynx.Rust.FormattingTest do
  use ExUnit.Case

  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_formatting/Properties.lean", __DIR__)
  @packages Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "kernel checks bounded formatting behavior and audits the complete runtime model", %{
    tmp_dir: tmp
  } do
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RustWorkspace"))
    path = Path.join(project, "RustWorkspace/Formatting.lean")
    File.cp!(@fixture, path)
    packages = @packages

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    Lynx.Rust.Project.ensure!(project, "RustWorkspace.Formatting", @tools)
    Lynx.Rust.Project.build!(project, ["RustWorkspace.Formatting"])
    source = File.read!(path)

    file = %{
      "module" => "RustWorkspace.Formatting",
      "file" => path,
      "imports" => ["Aeneas.Std.Core.Fmt", "Aeneas.Std.Scalar.Display"],
      "contents" => [],
      "preludes" => [%{"source" => source, "file" => path, "span" => [1], "indentation" => 0}],
      "audit_modules" => [
        "RustWorkspace.Formatting",
        "Aeneas.Std.Core.Fmt",
        "Aeneas.Std.Scalar.Display"
      ]
    }

    export = Path.join(tmp, "formatting.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
