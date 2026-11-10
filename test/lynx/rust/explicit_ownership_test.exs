defmodule Lynx.Rust.ExplicitOwnershipTest do
  use ExUnit.Case
  alias Lynx.Rust.{ExplicitOwnership, LLBCJson}

  @fixture Path.expand("../../fixtures/rust/explicit_ownership.json", __DIR__)
  @workspace Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")

  test "no-op instances retain compiler self identities and do not replace source bodies" do
    doc = @fixture |> File.read!() |> JSON.decode!()
    adapted = ExplicitOwnership.prepare!(doc)
    assert length(adapted.primitive_models) == 3
    assert Enum.all?(adapted.primitive_models, &(&1.implementation_verified == false))
    source = doc["translated"]
    target = adapted.document["translated"]
    assert length(target["fun_decls"]) == length(source["fun_decls"]) + 1

    for {before, after_} <- Enum.zip(source["fun_decls"], target["fun_decls"]) do
      impls = Enum.map(adapted.primitive_models, & &1.implementation_id)
      assert erase_witness(before, impls) == erase_witness(after_, impls)
    end

    assert %{
             "signature" => %{"is_unsafe" => true, "abi" => "Rust"},
             "body" => %{"Structured" => %{"locals" => %{"arg_count" => 1}}}
           } = List.last(target["fun_decls"])

    assert JSON.decode!(LLBCJson.encode_like!(adapted.document, @fixture)) == adapted.document
  end

  test "does not reinterpret an untracked or unsupported dictionary as no-op" do
    doc = @fixture |> File.read!() |> JSON.decode!()

    for dictionary <- ["UntrackedDestruct", "NoopDestruct"] do
      bad =
        alter(doc, fn
          %{"kind" => %{"BuiltinOrAuto" => %{"builtin_data" => "NoopDestruct"}}} = ref ->
            if dictionary == "UntrackedDestruct" do
              put_in(ref, ["kind", "BuiltinOrAuto", "builtin_data"], dictionary)
            else
              put_in(ref, ["trait_decl_ref", "generics", "types"], [
                %{"TypeVar" => %{"Free" => 0}}
              ])
            end

          other ->
            other
        end)

      if dictionary == "UntrackedDestruct" do
        assert %{primitive_models: []} = ExplicitOwnership.prepare!(bad)
      else
        assert_raise ArgumentError, fn -> ExplicitOwnership.prepare!(bad) end
      end
    end
  end

  test "requires intact compiler options, interfaces and declaration identities" do
    doc = @fixture |> File.read!() |> JSON.decode!()

    trait =
      Enum.find_index(
        doc["translated"]["trait_decls"],
        &(&1 && &1["item_meta"]["lang_item"] == "Destruct")
      )

    for bad <- [
          put_in(doc, ["has_errors"], true),
          put_in(doc, ["translated", "options", "precise_drops"], false),
          put_in(doc, ["translated", "options", "desugar_drops"], false),
          put_in(doc, ["translated", "trait_decls", Access.at(trait), "is_unsafe"], true),
          put_in(doc, ["translated", "fun_decls", Access.at(0), "def_id"], 9999)
        ] do
      assert_raise ArgumentError, fn -> ExplicitOwnership.prepare!(bad) end
    end
  end

  @tag timeout: 900_000
  @tag :tmp_dir
  @tag skip: is_nil(@tools) && "set LYNX_UNPATCHED_AENEAS_DIR for explicit ownership proofs"
  test "kernel-checks actual scalar and cross-crate observable destruction", %{tmp_dir: tmp} do
    tools = System.fetch_env!("LYNX_UNPATCHED_AENEAS_DIR")
    workspace = Path.join(tmp, "workspace")
    File.cp_r!(@workspace, workspace)
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Ownership"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.mkdir_p!(Path.join(project, ".lake"))
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    properties = File.read!(Path.join(@workspace, "Properties.lean"))
    property = Path.join(project, "Ownership/Properties.lean")
    File.write!(property, properties)

    verify = fn ->
      context = Lynx.Rust.Cargo.build!(workspace, "ownership-app", Path.join(tmp, "build"))
      raw = Path.join(project, "Source.llbc")

      args =
        [
          "rustc",
          "--sysroot",
          "default",
          "--preset",
          "aeneas",
          "--precise-drops",
          "--desugar-drops",
          "--start-from",
          "ownership_app::run",
          "--start-from",
          "ownership_app::run_scalar",
          "--include",
          "ownership_app",
          "--include",
          "ownership_base",
          "--opaque",
          "core",
          "--opaque",
          "alloc",
          "--opaque",
          "std",
          "--dest-file",
          raw,
          "--"
        ] ++
          Lynx.Rust.Cargo.extraction_arguments(context, project)

      {output, status} =
        System.cmd(Path.join(tools, "charon"), args,
          cd: context.record["directory"],
          env: Lynx.Rust.Cargo.environment(context),
          stderr_to_stdout: true
        )

      assert status == 0, output
      doc = File.read!(raw) |> JSON.decode!()
      adapted = ExplicitOwnership.prepare!(doc)
      backend = Path.join(project, "Ownership.llbc")
      File.write!(backend, LLBCJson.encode_like!(adapted.document, raw))

      {output, status} =
        System.cmd(
          Path.join(tools, "aeneas"),
          [
            "-backend",
            "lean",
            "-split-files",
            "-emit-json",
            "-abort-on-error",
            "-warnings-as-errors",
            "-dest",
            project,
            "-subdir",
            "Ownership",
            backend
          ],
          stderr_to_stdout: true
        )

      assert status == 0, output
      translated = File.read!(Path.join(project, "translation.json")) |> JSON.decode!()

      ids =
        for f <- doc["translated"]["fun_decls"],
            f && is_map(f["body"]) &&
              hd(f["item_meta"]["name"]) in [
                %{"Ident" => ["ownership_app", 0]},
                %{"Ident" => ["ownership_base", 0]}
              ],
            do: f["def_id"]

      implementations =
        Map.new(Enum.filter(translated["functions"], &(&1["def_id"] in ids)), &{&1["def_id"], &1})

      assert Enum.all?(Map.values(implementations), &(&1["is_opaque"] == false))
      Lynx.Rust.Project.ensure!(project, "Ownership", tools)
      Lynx.Rust.Project.build!(project, ["Ownership.Properties"])

      input =
        Lynx.Rust.Proofs.file!(
          %{
            module: "Ownership",
            implementations: implementations,
            audit_modules: ["Ownership.Types", "Ownership.Funs"]
          },
          ["Ownership.Properties"],
          required_properties:
            Enum.map(
              ~w(consume_contract scalar_finishes run_panics run_returns),
              &("Ownership.Properties." <> &1)
            )
        )

      input =
        Map.put(
          input,
          "cache_key",
          Lynx.Rust.Fingerprint.digest(
            File.read!(backend) <> properties <> File.read!(Path.join(tools, "lynx-toolchain"))
          )
        )

      {input, adapted}
    end

    {input, adapted} = verify.()
    refute adapted.primitive_models == []
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [input])
    assert [%{status: :ok, cached: true}] = Lynx.Commands.verify!(project, [input])
    export = Path.join(tmp, "ownership.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [input], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom hiddenOwnership : False",
          "private theorem unfinishedOwnership : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["Ownership.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [input])
    end

    File.write!(property, properties)
    source = Path.join(workspace, "base/src/lib.rs")
    File.write!(source, String.replace(File.read!(source), "self.code == 7", "self.code == 8"))
    assert_raise RuntimeError, ~r/native Lean project command failed/, fn -> verify.() end
  end

  defp erase_witness(
         %{
           "kind" => %{"BuiltinOrAuto" => %{"builtin_data" => "NoopDestruct"}},
           "trait_decl_ref" => declaration
         },
         _
       ),
       do: %{"dictionary" => declaration}

  defp erase_witness(
         %{"kind" => %{"TraitImpl" => %{"id" => id}}, "trait_decl_ref" => declaration} = map,
         ids
       ) do
    if id in ids,
      do: %{"dictionary" => declaration},
      else: Map.new(map, fn {k, v} -> {k, erase_witness(v, ids)} end)
  end

  defp erase_witness(map, ids) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, erase_witness(v, ids)} end)

  defp erase_witness(list, ids) when is_list(list), do: Enum.map(list, &erase_witness(&1, ids))
  defp erase_witness(value, _), do: value

  defp alter(map, fun) when is_map(map) do
    changed = fun.(map)
    if changed != map, do: changed, else: Map.new(map, fn {k, v} -> {k, alter(v, fun)} end)
  end

  defp alter(list, fun) when is_list(list), do: Enum.map(list, &alter(&1, fun))
  defp alter(value, _), do: value
end
