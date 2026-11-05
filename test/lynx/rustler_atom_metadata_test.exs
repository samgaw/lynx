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

      project = Path.join(tmp, "proofs")
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      project = Lynx.Rust.Project.ensure!(project, "AtomCache.Extraction", @tools)

      bridge = Lynx.Rustler.Bridge.install!(project, "AtomCache.Extraction")

      extraction =
        Lynx.Rust.Extraction.run!(
          context,
          @tools,
          [
            "experiment_nif::custom_encoding::invalid",
            "experiment_nif::custom_encoding::missing"
          ],
          project,
          "AtomCache.Extraction",
          rustler_atoms: [["custom_encoding"]],
          external_types: [
            %{
              rust: "rustler::types::atom::Atom",
              lean: "Lynx.Rustler.Atom",
              import: bridge,
              label: "Rustler logical atom FFI model"
            }
          ]
        )

      File.write!(Path.join(project, "AtomCache/Properties.lean"), """
      module
      public import AtomCache.Extraction.Funs
      public section
      open Aeneas Aeneas.Std
      namespace AtomCache.Properties
      theorem invalid : experiment_nif.custom_encoding.invalid = RustM.ok "invalid" := by
        simp [experiment_nif.custom_encoding.invalid, AtomCache.Extraction.RustlerAtomCache.cache_0]
      theorem missing : experiment_nif.custom_encoding.missing = RustM.ok "missing" := by
        simp [experiment_nif.custom_encoding.missing, AtomCache.Extraction.RustlerAtomCache.cache_0]
      end AtomCache.Properties
      """)

      Lynx.Rust.Project.build!(project, ["AtomCache.Properties"])

      proof =
        Lynx.Rust.Proofs.file!(extraction, ["AtomCache.Properties"],
          required_properties: ["AtomCache.Properties.invalid", "AtomCache.Properties.missing"]
        )

      export = Path.join(tmp, "atoms.export")
      reports = Lynx.Commands.verify!(project, [proof], export: export)
      assert Enum.all?(reports, &(&1.status == :ok))

      evidence =
        Lynx.Rust.Report.build!(extraction, reports, source_dir: context.record["directory"])

      assert length(evidence.guarantees) == 2

      assert [%{implementation_verified: false, status: :modelled}] =
               evidence.unverified_external_calls

      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      File.write!(Path.join(project, "AtomCache/Wrong.lean"), """
      module
      public import AtomCache.Extraction.Funs
      public section
      open Aeneas Aeneas.Std
      theorem wrong_atom : experiment_nif.custom_encoding.invalid = RustM.ok "missing" := by
        simp [experiment_nif.custom_encoding.invalid, AtomCache.Extraction.RustlerAtomCache.cache_0]
      """)

      {output, status} =
        System.cmd("lake", ["env", "lean", "AtomCache/Wrong.lean"],
          cd: project,
          stderr_to_stdout: true
        )

      assert status != 0
      assert output =~ "unsolved goals"

      assert [] = Lynx.Rustler.Metadata.atom_caches!(expanded, [["elsewhere"]])

      # Nominal paths are discovery hints; compiled identity and the actual
      # extracted Encoder are validated by preparation, not this parser.
      assert %{
               bindings: [
                 %{
                   "name" => "custom_validate",
                   "result" => %{"result" => [%{"tuple" => []}, %{"native" => ["Error"]}]}
                 }
               ]
             } =
               Lynx.Rustler.Metadata.bindings!(expanded, compiled, custom_validate: 1)

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
