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
             ] = caches = Lynx.Rustler.Metadata.atom_caches!(expanded, [["custom_encoding"]])

      %{document: document} =
        Lynx.Rust.Extraction.describe!(
          context,
          @tools,
          ["experiment_nif::custom_encoding::RustlerAtoms::get"],
          Path.join(tmp, "discovery"),
          "AtomCache.Extraction"
        )

      assert [
               %{
                 type_id: type_id,
                 factory_id: factory_id,
                 fields: fields,
                 implementation_verified: false
               }
             ] = Lynx.Rustler.AtomCaches.resolve!(document, caches)

      assert is_integer(type_id) and is_integer(factory_id)
      assert fields == hd(caches)["fields"]

      for changed <- [
            update_in(document, ["translated", "fun_decls"], fn functions ->
              Enum.map(functions, fn
                %{"def_id" => ^factory_id} = function ->
                  put_in(function, ["signature", "is_unsafe"], true)

                function ->
                  function
              end)
            end),
            update_in(document, ["translated", "global_decls"], fn globals ->
              Enum.map(globals, fn
                %{"global_kind" => %{"Static" => _}} = global ->
                  put_in(global, ["global_kind", "Static", "is_mut"], true)

                global ->
                  global
              end)
            end)
          ] do
        assert_raise ArgumentError, ~r/unsupported compiled Rustler atom cache/, fn ->
          Lynx.Rustler.AtomCaches.resolve!(changed, caches)
        end
      end

      # Nominal crate identity is checked independently of source spelling.
      for path <- [
            ~w(std sync once_lock OnceLock),
            ~w(rustler env OwnedEnv),
            ~w(rustler types atom Atom),
            ~w(core result Result)
          ] do
        original_name = Enum.map(path, &%{"Ident" => [&1, 0]})

        changed_document =
          update_in(document, ["translated", "type_decls"], fn types ->
            Enum.map(types, fn
              %{"item_meta" => %{"name" => ^original_name}} = type ->
                put_in(type, ["item_meta", "name"], [%{"Ident" => ["shadow", 0]} | original_name])

              type ->
                type
            end)
          end)

        assert_raise ArgumentError, ~r/unsupported compiled Rustler atom cache/, fn ->
          Lynx.Rustler.AtomCaches.resolve!(changed_document, caches)
        end
      end

      assert_raise ArgumentError, ~r/unsupported.*(global|static)/i, fn ->
        Lynx.Rust.LLBC.audit!(document, ["experiment_nif"])
      end

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
