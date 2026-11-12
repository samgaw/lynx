defmodule Lynx.Rust.DropTest do
  use ExUnit.Case
  alias Lynx.Rust.LLBC

  @tools System.get_env("LYNX_AENEAS_DIR")
  @packages Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "owned enum classification composes with checked structural destruction", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    for crate <- ~w(base analysis), do: File.mkdir_p!(Path.join([workspace, crate, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["base", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "base/Cargo.toml"), """
    [package]
    name = "drop-base"
    version = "0.1.0"
    edition = "2021"
    """)

    source = Path.join(workspace, "base/src/lib.rs")

    original = """
    pub enum Message {
        Code(u64),
        Text(String),
        Fixed(&'static str),
    }
    pub fn is_text(message: Message) -> bool {
        matches!(message, Message::Text(_))
    }
    """

    File.write!(source, original)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "drop-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    drop-base = { path = "../base" }
    """)

    File.write!(Path.join(workspace, "analysis/src/lib.rs"), """
    pub fn classify(message: drop_base::Message) -> bool {
        drop_base::is_text(message)
    }
    """)

    {output, status} =
      System.cmd(
        "cargo",
        ["generate-lockfile", "--manifest-path", Path.join(workspace, "Cargo.toml")],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "DropProofs"))

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "DropProofs/Properties.lean"), """
    module
    public import DropProofs.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace DropProofs
    theorem base_spec (message : drop_analysis.drop_base.Message) :
        drop_analysis.drop_base.is_text message = RustM.ok (match message with
          | .Text _ => true
          | _ => false) := by cases message <;> rfl
    theorem composed_spec (message : drop_analysis.drop_base.Message) :
        drop_analysis.classify message = RustM.ok (match message with
          | .Text _ => true
          | _ => false) := by
      simp [drop_analysis.classify, base_spec]
    end DropProofs
    """)

    options = [
      roots: ["drop_analysis::classify"],
      mir: :elaborated,
      lean_project: project,
      module_prefix: "DropProofs.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["DropProofs.Properties"],
      required_properties: ["DropProofs.composed_spec"]
    ]

    result = Lynx.Rust.verify!(workspace, "drop-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert [
             %{
               type: "alloc::string::String",
               status: :modelled,
               first_party: false,
               implementation_verified: false
             },
             %{
               type: "drop_base::Message",
               status: :audited_erasure,
               first_party: true,
               implementation_verified: false
             }
           ] = result.verification.structural_drops

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "native deallocation correctness are unverified")
           )

    assert "Lynx compiler-generated structural drop erasure audit" in result.verification.trusted_boundary

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract and row.theorem == "DropProofs.composed_spec" and
               "DropProofs.base_spec" in row.contracts_used
           end)

    for id <- Map.keys(result.extraction.audit.drops.erasures),
        do: refute(Map.has_key?(result.extraction.implementations, id))

    {owner, [_drop]} =
      Enum.find(result.extraction.audit.drops.sites, fn {_id, sites} -> sites != [] end)

    assert Enum.any?(
             result.verification.implementations,
             &(&1.definition_id == owner and &1.drop_effects != [])
           )

    document = JSON.decode!(File.read!(result.extraction.llbc))
    reject_inconsistent_erasure(document, result.extraction.audit)

    [first_party] =
      for {id, %{first_party: true}} <- result.extraction.audit.drops.erasures, do: id

    invalid =
      Map.update!(result.extraction.translation, "functions", &[%{"def_id" => first_party} | &1])

    assert_raise ArgumentError, ~r/did not erase/, fn ->
      LLBC.link!(result.extraction.audit, invalid)
    end

    export = Path.join(tmp, "drop.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["DropProofs.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    File.write!(source, String.replace(original, "Message::Text(_)", "Message::Code(_)"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "drop-analysis", options)
    end

    # Erasing this destructor would incorrectly turn a panicking computation into a total bool.
    File.write!(
      source,
      original <>
        """
        impl Drop for Message {
            fn drop(&mut self) { panic!(); }
        }
        """
    )

    assert_raise CompileError,
                 ~r/observable or unsupported behavior in compiler-generated drop glue/,
                 fn ->
                   Lynx.Rust.verify!(workspace, "drop-analysis", options)
                 end

    File.write!(source, String.replace(original, "Text(String)", "Text(Vec<u8>)"))

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "drop-analysis", options).reports

    File.write!(source, String.replace(original, "Text(String)", "Text(Box<u8>)"))

    assert_raise CompileError, ~r/owned drop type/, fn ->
      Lynx.Rust.verify!(workspace, "drop-analysis", options)
    end
  end

  defp reject_inconsistent_erasure(document, audit) do
    [own] = for {id, %{first_party: true}} <- audit.drops.erasures, do: id
    [external] = for {id, %{first_party: false}} <- audit.drops.erasures, do: id
    function = Enum.find(document["translated"]["fun_decls"], &(&1 && &1["def_id"] == own))
    impl = get_in(function, ["src", "TraitImpl", "impl_ref", "id"])
    trait = get_in(function, ["src", "TraitImpl", "trait_ref", "id"])
    bool = %{"Scalar" => "Bool"}

    changes = [
      change(document, "fun_decls", own, &put_in(&1, ["body"], "Opaque")),
      change(document, "fun_decls", own, &put_in(&1, ["signature", "is_unsafe"], false)),
      change(document, "fun_decls", own, &put_in(&1, ["signature", "output"], bool)),
      change(document, "fun_decls", own, &put_in(&1, ["src", "TraitImpl", "impl_ref", "id"], -1)),
      change(
        document,
        "fun_decls",
        own,
        &put_in(&1, ["src", "TraitImpl", "trait_ref", "id"], -1)
      ),
      change(document, "fun_decls", own, &put_in(&1, ["src", "TraitImpl", "item_id"], 1)),
      change(document, "fun_decls", external, &put_in(&1, ["signature", "inputs"], [bool])),
      change(
        document,
        "fun_decls",
        external,
        &put_in(&1, ["item_meta", "name", Access.at(0)], %{"Ident" => ["foreign", 0]})
      ),
      change(document, "trait_impls", impl, &put_in(&1, ["src"], "Normal")),
      change(
        document,
        "trait_impls",
        impl,
        &put_in(&1, ["methods", Access.at(0), "skip_binder", "id"], -1)
      ),
      change(
        document,
        "trait_impls",
        impl,
        &put_in(&1, ["impl_trait", "generics", "types"], [bool])
      ),
      change(
        document,
        "trait_decls",
        trait,
        &put_in(&1, ["item_meta", "name"], [%{"Ident" => ["lookalike", 0]}])
      ),
      change(document, "fun_decls", own, fn function ->
        update_in(
          function,
          ["body", "Structured", "body", "statements"],
          &[%{"kind" => "UnwindTerminate"} | &1]
        )
      end),
      change(document, "fun_decls", own, fn function ->
        update_in(
          function,
          ["body", "Structured", "body", "statements"],
          &[%{"kind" => %{"Call" => %{}}} | &1]
        )
      end),
      rewrite(document, fn
        %{"Drop" => drop} = node ->
          %{node | "Drop" => put_in(drop, ["fn_ptr", "kind", "Fun"], -1)}

        node ->
          node
      end),
      rewrite(document, fn
        %{"Drop" => drop} = node ->
          %{node | "Drop" => put_in(drop, ["fn_ptr", "generics", "types"], [bool])}

        node ->
          node
      end),
      rewrite(document, fn
        %{"Switch" => %{"data" => data} = switch} = node ->
          %{node | "Switch" => %{switch | "data" => %{data | "fallback" => 999}}}

        node ->
          node
      end)
    ]

    for {invalid, index} <- Enum.with_index(changes) do
      try do
        assert_raise CompileError, ~r/structural drop erasure rejected/, fn ->
          LLBC.audit!(invalid, ["drop_base", "drop_analysis"])
        end
      rescue
        error in ExUnit.AssertionError -> flunk("mutation #{index}: #{Exception.message(error)}")
      end
    end

    missing =
      update_in(
        document,
        ["translated", "fun_decls"],
        &Enum.reject(&1, fn f -> f && f["def_id"] == own end)
      )

    assert_raise CompileError, ~r/structural drop erasure rejected/, fn ->
      LLBC.audit!(missing, ["drop_base", "drop_analysis"])
    end
  end

  defp change(document, kind, id, fun),
    do:
      update_in(
        document,
        ["translated", kind],
        &Enum.map(&1, fn
          %{"def_id" => ^id} = item -> fun.(item)
          item -> item
        end)
      )

  defp rewrite(map, fun) when is_map(map),
    do: map |> Map.new(fn {k, v} -> {k, rewrite(v, fun)} end) |> fun.()

  defp rewrite(list, fun) when is_list(list), do: Enum.map(list, &rewrite(&1, fun))
  defp rewrite(value, _), do: value
end
