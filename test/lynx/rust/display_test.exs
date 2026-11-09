defmodule Lynx.Rust.DisplayTest do
  use ExUnit.Case
  alias Lynx.Rust.LLBC

  @tools System.get_env("LYNX_AENEAS_DIR")
  @packages Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "ToString invokes an actual cross-crate Display implementation", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    for name <- ~w(base analysis), do: File.mkdir_p!(Path.join([workspace, name, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["base", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "base/Cargo.toml"), """
    [package]
    name = "format-base"
    version = "0.1.0"
    edition = "2021"
    """)

    source = Path.join(workspace, "base/src/lib.rs")

    original = """
    pub struct Flag(pub bool);
    impl std::fmt::Display for Flag {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.0 { f.write_str("enabled") } else { f.write_str("disabled") }
        }
    }
    pub struct Fault(pub bool);
    impl std::fmt::Display for Fault {
        fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.0 { Err(std::fmt::Error) } else { panic!() }
        }
    }
    """

    File.write!(source, original)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "format-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    format-base = { path = "../base" }
    """)

    File.write!(Path.join(workspace, "analysis/src/lib.rs"), """
    pub fn describe(value: bool) -> String { format_base::Flag(value).to_string() }
    pub fn fault(value: bool) -> String { format_base::Fault(value).to_string() }
    """)

    {output, status} =
      System.cmd(
        "cargo",
        ["generate-lockfile", "--manifest-path", Path.join(workspace, "Cargo.toml")],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "DisplayProofs"))

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "DisplayProofs/Properties.lean"), """
    module
    public import DisplayProofs.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace DisplayProofs
    theorem flag_spec (value : Bool) (initial : String) :
        format_analysis.format_base.Flag.Insts.CoreFmtDisplay.fmt value initial =
          if value then Lynx.RustFormatting.Formatting.append initial "enabled" else Lynx.RustFormatting.Formatting.append initial "disabled" := by
      have yes : String.fromUTF8?
          ⟨(Lynx.RustFormatting.Formatting.bytes (toStr "enabled").val).toList.toArray⟩ = some "enabled" := by decide +kernel
      have no : String.fromUTF8?
          ⟨(Lynx.RustFormatting.Formatting.bytes (toStr "disabled").val).toList.toArray⟩ = some "disabled" := by decide +kernel
      cases value <;> simp [format_analysis.format_base.Flag.Insts.CoreFmtDisplay.fmt,
        Lynx.RustFormatting.core.fmt.Formatter.write_str, Lynx.RustFormatting.Formatting.writeBytes, yes, no]
    theorem describe_spec (value : Bool) :
        format_analysis.describe value = RustM.ok (if value then "enabled" else "disabled") := by
      have yes : "enabled".utf8ByteSize = 7 := by decide +kernel
      have no : "disabled".utf8ByteSize = 8 := by decide +kernel
      cases value <;> simp [format_analysis.describe, Lynx.RustFormatting.alloc.string.ToString.to_string,
        format_analysis.format_base.Flag.Insts.CoreFmtDisplay, flag_spec, Lynx.RustFormatting.Formatting.append, yes, no]
    theorem fault_spec (value : Bool) :
        format_analysis.fault value = RustM.fail .panic := by
      cases value <;> simp [format_analysis.fault, Lynx.RustFormatting.alloc.string.ToString.to_string,
        format_analysis.format_base.Fault.Insts.CoreFmtDisplay,
        format_analysis.format_base.Fault.Insts.CoreFmtDisplay.fmt, massert]
    end DisplayProofs
    """)

    options = [
      roots: ["format_analysis::describe", "format_analysis::fault"],
      lean_project: project,
      module_prefix: "DisplayProofs.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["DisplayProofs.Properties"],
      required_properties: ["DisplayProofs.describe_spec", "DisplayProofs.fault_spec"]
    ]

    result = Lynx.Rust.verify!(workspace, "format-analysis", options)

    assert [
             %{
               rust_name: "alloc::string::{alloc::string::ToString<@T>}::to_string",
               status: :modelled,
               implementation_verified: false
             },
             %{
               rust_name: "core::fmt::{core::fmt::Formatter<'a>}::write_str",
               status: :modelled,
               implementation_verified: false
             }
           ] = result.verification.unverified_external_calls

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract and row.theorem == "DisplayProofs.describe_spec" and
               "DisplayProofs.flag_spec" in row.contracts_used
           end)

    root =
      Enum.find_value(result.extraction.implementations, fn
        {id, %{"rust_name" => "format_analysis::describe"}} -> id
        _ -> nil
      end)

    [renderer] = result.extraction.audit.trait_dependencies[root]
    assert renderer in LLBC.dependencies(result.extraction.audit)[root]
    document = JSON.decode!(File.read!(result.extraction.llbc))
    reject_inconsistent_dictionaries(document, result.extraction.audit, renderer)

    export = Path.join(tmp, "display.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["DisplayProofs.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    # A changed first-party formatter must invalidate the caller's old property.
    File.write!(
      source,
      String.replace(original, "if self.0 { f.write_str", "if !self.0 { f.write_str")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "format-analysis", options)
    end
  end

  defp reject_inconsistent_dictionaries(document, audit, renderer) do
    {model_id, model} =
      Enum.find(audit.external_calls, fn {_id, model} -> Map.has_key?(model, :display_trait) end)

    function = Enum.find(audit.functions, &(&1["def_id"] == renderer))
    impl = get_in(function, ["src", "TraitImpl", "impl_ref", "id"])
    trait = model.display_trait
    boolean = %{"Scalar" => "Bool"}

    invalid = [
      change(document, "fun_decls", model_id, &put_in(&1, ["signature", "abi"], "C")),
      change(document, "fun_decls", model_id, &put_in(&1, ["signature", "output"], boolean)),
      change(
        document,
        "fun_decls",
        model_id,
        &put_in(&1, ["generics", "types"], [%{"index" => 1}])
      ),
      change(document, "fun_decls", model_id, &put_in(&1, ["generics", "trait_clauses"], [])),
      change(
        document,
        "trait_decls",
        trait,
        &put_in(&1, ["item_meta", "name"], [%{"Ident" => ["lookalike", 0]}])
      ),
      change(
        document,
        "trait_decls",
        trait,
        &put_in(&1, ["methods", Access.at(0), "params", "types"], [%{"index" => 0}])
      ),
      change(document, "trait_decls", trait, fn declaration ->
        update_in(
          declaration,
          ["methods", Access.at(0), "skip_binder", "signature", "inputs"],
          fn [_self, writer] ->
            [
              %{
                "Ref" => [
                  %{"Var" => %{"Bound" => [0, 0]}},
                  %{"TypeVar" => %{"Bound" => [0, 0]}},
                  "Shared"
                ]
              },
              writer
            ]
          end
        )
      end),
      change(document, "fun_decls", renderer, &put_in(&1, ["src", "TraitImpl", "item_id"], 1)),
      change(
        document,
        "fun_decls",
        renderer,
        &put_in(&1, ["src", "TraitImpl", "impl_ref", "id"], -1)
      ),
      change(
        document,
        "fun_decls",
        renderer,
        &put_in(&1, ["src", "TraitImpl", "trait_ref", "id"], -1)
      ),
      change(
        document,
        "fun_decls",
        renderer,
        &put_in(&1, ["src", "TraitImpl", "reuses_default"], true)
      ),
      change(document, "fun_decls", renderer, &put_in(&1, ["signature", "inputs"], [boolean])),
      change(document, "fun_decls", renderer, &put_in(&1, ["signature", "output"], boolean)),
      change(
        document,
        "trait_impls",
        impl,
        &put_in(&1, ["methods", Access.at(0), "skip_binder", "id"], model_id)
      ),
      change(
        document,
        "trait_impls",
        impl,
        &put_in(&1, ["methods", Access.at(0), "kind"], %{"TraitMethod" => [trait, 1]})
      ),
      change(document, "trait_impls", impl, &put_in(&1, ["impl_trait", "id"], -1)),
      change(
        document,
        "trait_impls",
        impl,
        &put_in(&1, ["impl_trait", "generics", "types"], [boolean])
      ),
      change(document, "trait_impls", impl, &put_in(&1, ["is_negative"], true)),
      change(document, "trait_impls", impl, &put_in(&1, ["is_unsafe"], true)),
      change(
        document,
        "trait_impls",
        impl,
        &put_in(&1, ["generics", "types"], [%{"index" => 0}])
      ),
      rewrite(document, fn
        %{"kind" => %{"TraitImpl" => %{"id" => ^impl}}} = ref ->
          put_in(ref, ["trait_decl_ref", "generics", "types"], [boolean])

        node ->
          node
      end)
    ]

    for {rejected, index} <- Enum.with_index(invalid) do
      try do
        assert_raise(CompileError, fn ->
          LLBC.audit!(rejected, ["format_base", "format_analysis"])
        end)
      rescue
        error in ExUnit.AssertionError -> flunk("mutation #{index}: #{Exception.message(error)}")
      end
    end

    # The promoted string-constant audit also requires the defining method body.
    opaque = change(document, "fun_decls", renderer, &put_in(&1, ["body"], "Opaque"))

    assert_raise ArgumentError, ~r/string constant has an inconsistent type/, fn ->
      LLBC.audit!(opaque, ["format_base", "format_analysis"])
    end

    missing =
      update_in(
        document,
        ["translated", "fun_decls"],
        &Enum.reject(&1, fn f -> f && f["def_id"] == renderer end)
      )

    # Removing the body also removes shared type definitions used by its literals.
    assert_raise ArgumentError, ~r/string constant has an inconsistent type/, fn ->
      LLBC.audit!(missing, ["format_base", "format_analysis"])
    end

    foreign =
      change(document, "fun_decls", renderer, fn function ->
        put_in(function, ["item_meta", "name", Access.at(0)], %{
          "Ident" => ["unverified_foreign", 0]
        })
      end)

    assert_raise CompileError,
                 ~r/monomorphic extracted implementation or approved typed renderer/,
                 fn ->
                   LLBC.audit!(foreign, ["format_base", "format_analysis"])
                 end
  end

  defp change(document, kind, id, fun) do
    update_in(
      document,
      ["translated", kind],
      &Enum.map(&1, fn
        %{"def_id" => ^id} = item -> fun.(item)
        item -> item
      end)
    )
  end

  defp rewrite(map, fun) when is_map(map),
    do: map |> Map.new(fn {k, v} -> {k, rewrite(v, fun)} end) |> fun.()

  defp rewrite(list, fun) when is_list(list), do: Enum.map(list, &rewrite(&1, fun))
  defp rewrite(value, _), do: value
end
