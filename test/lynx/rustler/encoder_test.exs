defmodule Lynx.Rustler.EncoderTest do
  use ExUnit.Case

  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for compiled Rustler Encoder proofs")

  for version <- ["0.38.0", "0.39.0"] do
    @tag tmp_dir: "process-#{System.pid()}"
    test "proves the actual custom Encoder with Rustler #{version}", %{tmp_dir: tmp} do
      version = unquote(version)
      workspace = Path.join(tmp, "workspace")
      File.mkdir_p!(workspace)

      for file <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
          do: File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))

      manifest = Path.join(workspace, "nif/Cargo.toml")
      File.write!(manifest, String.replace(File.read!(manifest), "=0.39.0", "=#{version}"))

      {output, status} =
        System.cmd(
          "cargo",
          ["update", "--manifest-path", manifest, "-p", "rustler", "--precise", version],
          stderr_to_stdout: true
        )

      assert status == 0, output

      context =
        Lynx.Rust.Cargo.build!(workspace, "experiment-nif", Path.join(tmp, "build"),
          features: ["custom-encoder"]
        )

      assert Lynx.Rustler.require_rustler!(context) == version

      unsupported =
        update_in(context.workspace.packages, fn packages ->
          Map.new(packages, fn {id, package} ->
            {id,
             if(package["name"] == "rustler",
               do: Map.put(package, "version", "99.0.0"),
               else: package
             )}
          end)
        end)

      assert_raise ArgumentError, ~r/requires a direct Rustler 0.38.0 or 0.39.0 dependency/, fn ->
        Lynx.Rust.Extraction.run!(
          unsupported,
          @tools,
          ["unused"],
          Path.join(tmp, "unsupported"),
          "EncoderProof.Extraction",
          external_calls: [:rustler_encoders]
        )
      end

      project = Path.join(tmp, "proofs")
      packages = Path.join(@fixture, "proofs/.lake/packages")

      if File.dir?(packages) do
        File.mkdir_p!(Path.join(project, ".lake"))
        File.ln_s!(packages, Path.join(project, ".lake/packages"))
      end

      project = Lynx.Rust.Project.ensure!(project, "EncoderProof.Extraction", @tools)
      bridge = Lynx.Rustler.Bridge.install!(project, "EncoderProof.Extraction")

      models =
        for {rust, lean} <- [
              {"rustler::env::Env", "Env"},
              {"rustler::term::Term", "NativeTerm"},
              {"rustler::types::atom::Atom", "Atom"}
            ],
            do: %{
              rust: rust,
              lean: "Lynx.Rustler." <> lean,
              import: bridge,
              label: "Stateless Rustler term-construction FFI model"
            }

      extraction =
        Lynx.Rust.Extraction.run!(
          context,
          @tools,
          ["{impl rustler::Encoder for experiment_nif::custom_encoding::Error}::encode"],
          project,
          "EncoderProof.Extraction",
          rustler_atoms: [["custom_encoding"]],
          external_types: models,
          external_calls: [:rustler_encoders]
        )

      encoder =
        Enum.find(Map.values(extraction.implementations), fn implementation ->
          List.last(implementation["declaration"]["item_meta"]["name"]) == %{
            "Ident" => ["encode", 0]
          }
        end)

      assert encoder != nil
      implementations = Enum.map(Map.values(extraction.implementations), & &1["lean_name"])
      dictionaries = Enum.map(extraction.translation["trait_impls"], & &1["lean_name"])

      unfold =
        Enum.join(
          implementations ++
            dictionaries ++
            [
              "EncoderProof.Extraction.RustlerAtomCache.cache_0",
              "Lynx.Rustler.Encoding.pair",
              "Lynx.Rustler.Encoding.shared",
              "Lynx.Rustler.Encoding.string",
              "Lynx.Rustler.Encoding.atom"
            ],
          ", "
        )

      File.write!(Path.join(project, "EncoderProof/Properties.lean"), """
      module
      public import EncoderProof.Extraction.Funs
      public section
      open Aeneas Aeneas.Std
      namespace EncoderProof.Properties
      theorem invalid (message : String) (bounded : message.toUTF8.size ≤ 4294967295) :
          #{encoder["lean_name"]} (.Invalid message) () =
            RustM.ok (.tuple #[.atom "invalid", .bitstring message.toUTF8 0]) := by
        simp_all [#{unfold}]
      theorem missing : #{encoder["lean_name"]} .Missing () = RustM.ok (.atom "missing") := by
        simp_all [#{unfold}]
      theorem oversized (message : String) (outside : ¬ message.toUTF8.size ≤ 4294967295) :
          #{encoder["lean_name"]} (.Invalid message) () = RustM.fail .undef := by
        simp only [#{unfold}, outside, if_neg, bind_ok, bind_fail]
        simp
      end EncoderProof.Properties
      """)

      Lynx.Rust.Project.build!(project, ["EncoderProof.Properties"])

      proof =
        Lynx.Rust.Proofs.file!(extraction, ["EncoderProof.Properties"],
          required_properties: [
            "EncoderProof.Properties.invalid",
            "EncoderProof.Properties.missing",
            "EncoderProof.Properties.oversized"
          ]
        )

      export = Path.join(tmp, "encoder.export")
      assert [%{status: :ok}] = reports = Lynx.Commands.verify!(project, [proof], export: export)

      report =
        Lynx.Rust.Report.build!(extraction, reports, source_dir: context.record["directory"])

      assert Enum.any?(report.guarantees, &(&1.rust_name == encoder["rust_name"]))
      assert Enum.all?(report.unverified_external_calls, &(&1.implementation_verified == false))
      sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)

      assert status == 0, output

      # Generic dictionaries must resolve to actual methods, not assumed
      # contracts or same-signature methods from different implementations.
      model =
        Enum.find(
          Map.values(extraction.audit.external_calls),
          &(&1.lean == "Lynx.Rustler.Encoding.string")
        )

      shared =
        Enum.find(
          Map.values(extraction.audit.external_calls),
          &(&1.lean == "Lynx.Rustler.Encoding.shared")
        )

      assert {:error, _, message} =
               Lynx.Rustler.EncoderModels.audit(
                 extraction.audit.functions,
                 Map.delete(extraction.audit.external_calls, model.definition_id),
                 extraction.audit.translated,
                 extraction.audit.references
               )

      assert message =~ "matching dictionary"

      impl_id = shared.function["src"]["TraitImpl"]["impl_ref"]["id"]

      changed =
        update_in(extraction.audit.translated, ["trait_impls"], fn impls ->
          Enum.map(impls, fn
            %{"def_id" => ^impl_id} = impl ->
              put_in(impl, ["methods", Access.at(0), "skip_binder", "id"], model.definition_id)

            impl ->
              impl
          end)
        end)

      assert {:error, _, message} =
               Lynx.Rustler.EncoderModels.audit(
                 extraction.audit.functions,
                 extraction.audit.external_calls,
                 changed,
                 extraction.audit.references
               )

      assert message =~ "matching dictionary"

      File.write!(Path.join(project, "EncoderProof/Wrong.lean"), """
      module
      public import EncoderProof.Extraction.Funs
      public section
      open Aeneas Aeneas.Std
      theorem wrong : #{encoder["lean_name"]} .Missing () = RustM.ok (.atom "invalid") := by
        simp_all [#{unfold}]
      """)

      {output, status} =
        System.cmd("lake", ["env", "lean", "EncoderProof/Wrong.lean"],
          cd: project,
          stderr_to_stdout: true
        )

      assert status != 0
      assert output =~ "unsolved goals"
    end
  end
end
