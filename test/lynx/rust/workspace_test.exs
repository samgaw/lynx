defmodule Lynx.Rust.WorkspaceTest do
  use ExUnit.Case, async: true

  alias Lynx.Rust.Workspace

  @manifest Path.expand("../../fixtures/rust_workspace/Cargo.toml", __DIR__)

  test "discovers resolved workspace packages in dependency order" do
    assert {:ok, %{root: root, crates: crates}} = Workspace.discover(@manifest)
    assert root == Path.dirname(@manifest)

    assert Enum.sort(Enum.map(crates, & &1.name)) ==
             ["experiment-analysis", "experiment-core", "experiment-nif", "experiment-unrelated"]

    core = Enum.find(crates, &(&1.name == "experiment-core"))
    analysis = Enum.find(crates, &(&1.name == "experiment-analysis"))
    unrelated = Enum.find(crates, &(&1.name == "experiment-unrelated"))
    assert analysis.dependencies == [core.id]
    assert core.dependencies == []
    assert unrelated.dependencies == []
    nif = Enum.find(crates, &(&1.name == "experiment-nif"))
    assert nif.dependencies == [analysis.id]
    assert [_rustler] = nif.external_dependencies
    assert Enum.all?([core, analysis, unrelated], &(&1.external_dependencies == []))

    assert Enum.find_index(crates, &(&1.id == core.id)) <
             Enum.find_index(crates, &(&1.id == analysis.id))
  end

  @tag :tmp_dir
  test "dev dependency cycles do not affect library verification order", %{tmp_dir: tmp} do
    File.write!(
      Path.join(tmp, "Cargo.toml"),
      "[workspace]\nmembers = [\"first\", \"second\"]\nresolver = \"2\"\n"
    )

    for {name, deps} <- [
          {"first", "[dev-dependencies]\nsecond = { path = \"../second\" }\n"},
          {"second", "[dependencies]\nfirst = { path = \"../first\" }\n"}
        ] do
      File.mkdir_p!(Path.join([tmp, name, "src"]))
      File.write!(Path.join([tmp, name, "src/lib.rs"]), "pub fn value() -> bool { true }\n")

      File.write!(
        Path.join([tmp, name, "Cargo.toml"]),
        "[package]\nname = \"#{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n" <> deps
      )
    end

    manifest = Path.join(tmp, "Cargo.toml")

    {output, status} =
      System.cmd("cargo", ["generate-lockfile", "--manifest-path", manifest],
        stderr_to_stdout: true
      )

    assert status == 0, output

    assert {:ok,
            %{crates: [%{name: "first", dependencies: []}, %{name: "second", dependencies: [_]}]}} =
             Workspace.discover(manifest)
  end

  test "reports cargo metadata errors" do
    assert {:error, message} = Workspace.discover(@manifest <> ".missing")
    assert message =~ "cargo metadata failed"
  end
end
