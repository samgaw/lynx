defmodule Lynx.Rust.OwnedResourceTest do
  use ExUnit.Case
  alias Lynx.Rust.{CallModels, NativeOwnedDrops, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "+owned-drops-v1"
               )
  unless @available, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-drops backend")

  @tag :tmp_dir
  test "proves shared resource mutation and actual final payload cleanup", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Resource"))

    for {fixture, name} <- [
          {"NativeOwnedResource.lean", "Properties"},
          {"NativeResourceCritical.lean", "Critical"}
        ],
        do: File.cp!(Path.join(@fixture, fixture), Path.join(project, "Resource/#{name}.lean"))

    property = Path.join(project, "Resource/Properties.lean")
    original = File.read!(property)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::resource_cycle"],
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Resource.Extraction",
      proof_modules: ["Resource.Critical", "Resource.Properties"],
      required_properties:
        Enum.map(
          ~w(construct_next construct unregistered_cleanup payload_cleanup_next final_release_next clone_next nonfinal_release_next update_next complete_cycle),
          &("Resource.Properties." <> &1)
        ) ++
          ["Resource.Critical.increment_spec", "Resource.Critical.critical_state_next"]
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert [%{lean_name: "effects_native.CounterResource.drop_owned"}] =
             result.verification.resource_cleanup

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    audit = result.extraction.audit
    t = audit.translated

    resource =
      Enum.find(
        t["type_decls"],
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["CounterResource", 0]})
      )

    payload = %{
      "Adt" => %{
        "id" => resource["def_id"],
        "builtin" => nil,
        "generics" => Lynx.Rust.ResourceModels.args([])
      }
    }

    destructor = NativeOwnedDrops.function_for(payload, t, audit.references)
    assert destructor

    for altered <- [
          put_in(t, ["options", "owned_drops"], false),
          update_in(t, ["fun_decls"], &(&1 ++ [destructor])),
          update_in(t, ["fun_decls"], fn fs ->
            Enum.map(fs, fn f ->
              if f == destructor,
                do:
                  put_in(f, ["body", "Structured", "body", "statements"], [
                    %{"kind" => %{"Panic" => %{}}}
                  ]),
                else: f
            end)
          end)
        ] do
      refute NativeOwnedDrops.function_for(payload, altered, audit.references)
    end

    # Exercise the nonpanicking consuming-callee check without an earlier
    # compiler-unwind rejection hiding the caller's retained ownership.
    release =
      Enum.find(
        audit.functions,
        &(List.last(&1["item_meta"]["name"]) == %{"Ident" => ["resource_release", 0]})
      )

    panicking =
      update_in(release, ["body", "Structured", "body", "statements"], fn statements ->
        [%{"kind" => %{"Panic" => %{"on_unwind" => %{"statements" => []}}}} | statements]
      end)

    functions = Enum.map(audit.functions, fn f -> if f == release, do: panicking, else: f end)

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      Lynx.Rust.NativeLifetimes.audit!(functions, audit.external_calls, t, audit.references)
    end

    generated = File.read!(Path.join(project, "Resource/Extraction/Funs.lean"))
    assert String.contains?(generated, "cleanup := effects_native.CounterResource.drop_owned")
    assert String.contains?(generated, "Lynx.NativeResourceArc.newOwned")
    assert String.contains?(generated, "Lynx.NativeOwnedDrop.drop resource")

    drop =
      Enum.find(
        t["fun_decls"],
        &(&1 &&
            &1["item_meta"]["name"] ==
              Enum.map(~w(core mem drop), fn n -> %{"Ident" => [n, 0]} end))
      )

    assert %{lean: "Lynx.NativeOwnedDrop.drop"} =
             CallModels.resolve([drop], t, audit.references, [], :runtime)[drop["def_id"]]

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "owned-resource.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom resourceTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, ["Resource.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    wrong =
      String.replace(
        original,
        "next () {env with nativeRefCounter := counter, nativeHeap := []}",
        "next () (live env value token counter)"
      )

    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, ["Resource.Properties"])
    end

    File.write!(property, original)
    native = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(native)

    changed =
      String.replace(
        source,
        "let changed = resource_locked_increment(&retained, amount);",
        "let changed = resource_locked_increment(&retained, 0);"
      )

    refute changed == source
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(native, source)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports

    # Real compiler unwind cleanup for another live alias is still unsupported.
    File.write!(
      native,
      source <>
        """

        pub fn release_then_assert(resource: rustler::ResourceArc<CounterResource>, accepted: bool) {
            drop(resource);
            assert!(accepted);
        }
        pub fn resource_panic_alias(value: u64, accepted: bool) {
            let first = resource_new(value);
            let retained = resource_clone(&first);
            release_then_assert(first, accepted);
            resource_release(retained);
        }
        """
    )

    assert_raise CompileError, ~r/Rust structural drop erasure rejected/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "effects-native",
        Keyword.put(options, :roots, ["effects_native::resource_panic_alias"])
      )
    end
  end

  @tag :tmp_dir
  test "rejects recursive resource cleanup before following its destructor dictionaries", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    native = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      native,
      File.read!(native) <>
        """

        pub struct RecursiveResource { next: rustler::ResourceArc<RecursiveResource> }
        #[rustler::resource_impl]
        impl rustler::Resource for RecursiveResource {}
        pub fn recursive_resource_clone(value: &rustler::ResourceArc<RecursiveResource>) -> rustler::ResourceArc<RecursiveResource> {
            value.clone()
        }
        """
    )

    project = Path.join(tmp, "proofs")
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    assert_raise CompileError,
                 ~r/resource call requires a concrete default Resource implementation/,
                 fn ->
                   Lynx.Rust.verify!(workspace, "effects-native",
                     roots: ["effects_native::recursive_resource_clone"],
                     tools: @tools,
                     execution: :runtime,
                     owned_drops: true,
                     lean_project: project,
                     build_dir: Path.join(tmp, "build"),
                     module_prefix: "Recursive.Extraction"
                   )
                 end
  end
end
