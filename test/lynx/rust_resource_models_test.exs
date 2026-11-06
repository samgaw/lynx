defmodule Lynx.Rust.ResourceModelsTest do
  use ExUnit.Case
  alias Lynx.Rust.{CallModels, Cargo, Extraction, LLBC, Project, ResourceModels, Runtime}
  @fixture Path.expand("../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "needs-drop-v1")
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned compiler-drop-query backend")

  @tag :tmp_dir
  test "checks actual resource methods and concrete destructor-free Resource dictionaries", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    context = Cargo.build!(workspace, "effects-native", Path.join(tmp, "build"), [])

    raw =
      Extraction.describe!(
        context,
        @tools,
        ["effects_native::scalar_resource_cycle"],
        Path.join(tmp, "raw"),
        "Resource.Extraction"
      )

    translated = raw.document["translated"]
    refs = LLBC.type_references!(raw.document)
    functions = Enum.reject(translated["fun_decls"], &is_nil/1)
    methods = for f <- functions, m = ResourceModels.resolve(f, translated, refs), do: {f, m}

    assert Enum.sort(Enum.map(methods, fn {_, m} -> m.resource_operation end)) ==
             ~w(clone deref new)

    assert Enum.any?(
             functions,
             &(&1["item_meta"]["name"] == path(~w(effects_core counter_value)))
           )

    for {function, model} <- methods do
      assert %{builtin: false, can_fail: true, lift: true} = model

      for invalid <- [
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "inputs"], []),
            put_in(function, ["generics", "trait_clauses"], []),
            put_in(function, ["item_meta", "name"], path(~w(shadow new)))
          ],
          do: assert(is_nil(ResourceModels.resolve(invalid, translated, refs)))

      [arc] = Enum.filter(translated["type_decls"], &ResourceModels.type?/1)
      duplicate = Map.update!(translated, "type_decls", &[arc | &1])
      assert is_nil(ResourceModels.resolve(function, duplicate, refs))

      if model.resource_operation != "new" do
        impl_id = function["src"]["TraitImpl"]["impl_ref"]["id"]

        altered =
          update_in(translated, ["trait_impls"], fn implementations ->
            Enum.map(implementations, fn impl ->
              if impl && impl["def_id"] == impl_id,
                do: put_in(impl, ["generics", "trait_clauses"], []),
                else: impl
            end)
          end)

        assert is_nil(ResourceModels.resolve(function, altered, refs))

        assert is_nil(
                 ResourceModels.resolve(
                   put_in(function, ["src", "TraitImpl", "reuses_default"], true),
                   translated,
                   refs
                 )
               )
      end
    end

    models = CallModels.resolve(functions, translated, refs, [], :runtime)
    assert Enum.any?(models, fn {_, m} -> m[:native_resource_type] end)
    assert :ok = Lynx.Rust.ResourceAudit.audit(functions, models, translated, refs)
    assert :ok = Lynx.Rust.NativeDrops.audit(functions, models, translated, refs)

    changed =
      update_in(translated, ["fun_decls"], fn declarations ->
        Enum.map(declarations, fn f ->
          if f && List.last(f["item_meta"]["name"]) == %{"Builtin" => ["DropGlue", 0]},
            do: put_in(f, ["signature", "is_unsafe"], false),
            else: f
        end)
      end)

    assert {:error, _, _} = Lynx.Rust.NativeDrops.audit(functions, models, changed, refs)

    resource =
      Enum.find(translated["type_decls"], fn type ->
        type && type["item_meta"]["name"] == path(~w(effects_native ScalarResource))
      end)

    for invalid <- [nil, true] do
      changed =
        update_in(translated, ["type_decls"], fn types ->
          Enum.map(types, fn type ->
            if type && type["def_id"] == resource["def_id"],
              do: Map.put(type, "needs_drop", invalid),
              else: type
          end)
        end)

      assert {:error, _, _} = Lynx.Rust.ResourceAudit.audit(functions, models, changed, refs)
    end

    changed =
      update_in(translated, ["trait_impls"], fn implementations ->
        Enum.map(implementations, fn impl ->
          if impl && impl["methods"] == [nil, nil],
            do: Map.put(impl, "methods", [%{"custom" => true}, nil]),
            else: impl
        end)
      end)

    assert {:error, _, _} = Lynx.Rust.ResourceAudit.audit(functions, models, changed, refs)

    changed =
      update_in(translated, ["global_decls"], fn globals ->
        Enum.map(globals, fn global ->
          if global && match?(%{"TraitDefault" => _}, global["src"]),
            do: Map.put(global, "src", "Normal"),
            else: global
        end)
      end)

    assert {:error, _, _} = Lynx.Rust.ResourceAudit.audit(functions, models, changed, refs)

    assert_raise CompileError, fn ->
      LLBC.audit!(raw.document, raw.first_party, execution: :pure)
    end
  end

  @tag :tmp_dir
  test "kernel checks resource model ownership and audits its private declarations", %{
    tmp_dir: tmp
  } do
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    if File.dir?(packages), do: File.ln_s!(packages, Path.join(project, ".lake/packages"))
    Project.ensure!(project, "Resource", @tools)
    Runtime.configuration!(:runtime, project, "Resource.Extraction")
    property = Path.join(project, "Resource/ModelProperties.lean")
    File.cp!(Path.join(@fixture, "NativeResourceModel.lean"), property)
    Project.build!(project, ["Resource.ModelProperties"])

    file = %{
      "module" => "Resource.Audit",
      "file" => "Resource.Audit.lean",
      "imports" => ["Resource.ModelProperties"],
      "contents" => [],
      "audit_modules" => ["Resource.ModelProperties", "Resource.NativeRuntime"],
      "preludes" => []
    }

    export = Path.join(tmp, "model.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    original = File.read!(property)
    File.write!(property, String.replace(original, "env.refCounter + 3", "env.refCounter + 2"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, ["Resource.ModelProperties"])
    end

    File.write!(property, original <> "\nprivate axiom uncheckedResource : False\n")
    Project.build!(project, ["Resource.ModelProperties"])
    assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
  end

  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})
end
