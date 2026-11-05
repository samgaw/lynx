defmodule Lynx.RustlerAtomMetadataTest do
  use ExUnit.Case

  @fixture Path.expand("../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for native Cargo integration tests")

  for version <- ["0.38.0", "0.39.0"] do
    @tag tmp_dir: "process-#{System.pid()}"
    test "discovers the actual generated atom cache under Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for name <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
          do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))

      {output, status} =
        System.cmd(
          "cargo",
          [
            "update",
            "--manifest-path",
            manifest,
            "-p",
            "rustler",
            "--precise",
            version
          ],
          stderr_to_stdout: true
        )

      assert status == 0, output

      context =
        Lynx.Rust.Cargo.build!(workspace, "experiment-nif", Path.join(tmp, "build"),
          features: ["custom-encoder"]
        )

      expanded = Path.join(tmp, "expanded.rs")
      File.write!(expanded, Lynx.Rust.Cargo.expand!(context))

      [library] =
        Enum.filter(context.artifact["filenames"], &(Path.extname(&1) in [".dylib", ".so"]))

      compiled = Lynx.Rustler.Metadata.inspect!(library)
      assert {"custom_validate", 1, 0} in compiled.exports

      assert %{bindings: [%{"name" => "restore", "arguments" => ["bool"], "result" => "bool"}]} =
               Lynx.Rustler.Metadata.bindings!(expanded, compiled, restore: 1)

      assert [
               %{
                 "modules" => ["custom_encoding"],
                 "structure" => "RustlerAtoms",
                 "fields" => [
                   %{"field" => "invalid", "atom" => "invalid"},
                   %{"field" => "missing", "atom" => "missing"}
                 ]
               }
             ] = Lynx.Rustler.Metadata.atom_caches!(expanded, [["custom_encoding"]])

      assert [] = Lynx.Rustler.Metadata.atom_caches!(expanded, [["elsewhere"]])

      # Metadata discovery alone does not admit this unimplemented codec.
      assert_raise RuntimeError, ~r/cannot discover Rustler bindings/, fn ->
        Lynx.Rustler.Metadata.bindings!(expanded, compiled, custom_validate: 1)
      end

      original = File.read!(expanded)
      changed = String.replace(original, "RUSTLER_ATOMS.get_or_init", "RUSTLER_ATOMS.get")
      assert original != changed
      File.write!(expanded, changed)

      assert_raise RuntimeError, ~r/unsupported RustlerAtoms cache initialization/, fn ->
        Lynx.Rustler.Metadata.atom_caches!(expanded, [["custom_encoding"]])
      end
    end
  end
end
