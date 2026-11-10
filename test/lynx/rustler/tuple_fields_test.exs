defmodule Lynx.Rustler.TupleFieldsTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_UNPATCHED_AENEAS_DIR for internal tuple proofs")

  for version <- ["0.38.0", "0.39.0"] do
    @tag :tmp_dir
    test "proves actual internal tuple extraction with Rustler #{version}", %{tmp_dir: tmp} do
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for name <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
          do: File.cp_r!(Path.join(@fixture, name), Path.join(workspace, name))

      manifest = Path.join(workspace, "nif/Cargo.toml")
      version = unquote(version)
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output
      native = Path.join(workspace, "nif/src/lib.rs")

      source =
        "#![feature(register_tool)]\n#![register_tool(verify)]\n" <>
          Enum.reduce(~w(tuple_fields tuple_size decoded_flag), File.read!(native), fn name, s ->
            String.replace(s, "fn #{name}(", "#[verify::start_from]\nfn #{name}(")
          end)

      # Internal proof roots are public; keep attributes before visibility.
      source = String.replace(source, "pub #[verify::start_from]", "#[verify::start_from]\npub")

      File.write!(native, source)
      project = Path.join(tmp, "proofs")
      File.mkdir_p!(Path.join(project, "TupleFields"))
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      property = Path.join(project, "TupleFields/Properties.lean")
      properties = File.read!(Path.join(@fixture, "proofs/RustWorkspace/TupleFields.lean"))
      File.write!(property, properties)

      options = [
        workspace: workspace,
        package: "experiment-nif",
        tools: @tools,
        root_attribute: "verify::start_from",
        cargo: [features: ["custom-decoder"]],
        only: [decoded_flag: 2],
        proof_roots: ["experiment_nif::tuple_fields", "experiment_nif::tuple_size"],
        build_dir: Path.join(tmp, "build"),
        lean_project: project,
        module_prefix: "TupleFields.Extraction",
        proof_modules: ["TupleFields.Properties"],
        required_properties:
          Enum.map(
            ~w(fields_spec rejected_spec oversized_spec size_spec size_rejected_spec),
            &("TupleFields.Properties." <> &1)
          )
      ]

      verified = Lynx.Rustler.prepare!(options)
      assert Enum.all?(verified.reports, &(&1.status == :ok))
      refute Enum.any?(verified.bindings.exports, fn {name, _, _} -> name == "tuple_fields" end)

      assert Enum.any?(
               verified.verification.guarantees,
               &(&1.kind == :rust_implementation and
                   &1.theorem == "TupleFields.Properties.fields_spec")
             )

      assert Enum.any?(
               verified.verification.unverified_external_calls,
               &(&1.rust_name == "rustler::types::tuple::get_tuple" and
                   &1.implementation_verified == false)
             )

      assert Enum.any?(verified.verification.structural_drops, fn entry ->
               entry.type == "alloc::vec::Vec<rustler::term::Term>" and
                 entry.element_drop_basis.kind == :compiler_copy and
                 entry.implementation_verified == false
             end)

      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

      file =
        Lynx.Rust.Proofs.file!(verified.extraction, options[:proof_modules],
          required_properties: options[:required_properties]
        )

      export = Path.join(tmp, "tuple.export")
      assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      for extra <- [
            "private axiom tupleTrust : False",
            "private theorem unfinishedTuple : True := by sorry"
          ] do
        File.write!(property, properties <> "\n" <> extra <> "\n")
        assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
      end

      File.write!(property, properties)

      changed =
        String.replace(
          source,
          "rustler::types::tuple::get_tuple(input)",
          "Err(rustler::Error::BadArg)",
          global: false
        )

      refute changed == source
      File.write!(native, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      changed = String.replace(source, "Ok(fields.len())", "Ok(fields.len() + 1)")
      refute changed == source
      File.write!(native, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

      File.write!(native, source)
      assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
    end
  end
end
