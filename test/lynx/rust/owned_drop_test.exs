defmodule Lynx.Rust.OwnedDropTest do
  use ExUnit.Case
  alias Lynx.Rust.{LLBC, Project, Proofs}
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
  test "proves actual compiler cleanup of an owned first-party mutex payload", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Owned"))
    property = Path.join(project, "Owned/Properties.lean")
    original = File.read!(Path.join(@fixture, "NativeOwnedDrop.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::owned_counter_payload"],
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Owned.Extraction",
      proof_modules: ["Owned.Properties"],
      required_properties:
        Enum.map(~w(construct cleanup construct_cleanup), &("Owned.Properties." <> &1))
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports
    assert result.verification.owned_drops

    assert Enum.any?(
             result.verification.implementations,
             &(&1.lean_name == "effects_native.CounterResource.drop_owned")
           )

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "actual optimized rustc drop MIR")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    # An emitted body without a corresponding Lean implementation is insufficient.
    missing =
      update_in(result.extraction.translation, ["functions"], fn functions ->
        Enum.reject(
          functions,
          &(&1["rust_name"] == "effects_native::CounterResource::drop_owned")
        )
      end)

    refute missing == result.extraction.translation

    assert_raise CompileError, ~r/missing, ambiguous or opaque Aeneas implementation/, fn ->
      LLBC.link!(result.extraction.audit, missing, result_monad: "Lynx.NativeM")
    end

    file =
      Proofs.file!(result.extraction, ["Owned.Properties"],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "owned.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom nativeTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, ["Owned.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(
      property,
      String.replace(
        original,
        "refCounter := env.refCounter + 1",
        "refCounter := env.refCounter + 2"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, ["Owned.Properties"])
    end

    File.write!(property, original)
    native = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(native)

    constructor = """
    pub fn owned_counter_payload(value: u64) -> CounterResource {
        CounterResource {
            state: Mutex::new(effects_core::Counter { value }),
        }
    }
    """

    changed =
      String.replace(
        source,
        constructor,
        constructor
        |> String.replace("(value: u64)", "(_value: u64)")
        |> String.replace("Counter { value }", "Counter { value: 0 }")
      )

    refute changed == source
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(native, source)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports

    File.write!(
      native,
      source <>
        """

        pub struct UnsupportedOwned { state: std::sync::RwLock<u64> }
        pub fn unsupported_owned(value: u64) -> UnsupportedOwned {
            UnsupportedOwned { state: std::sync::RwLock::new(value) }
        }
        """
    )

    assert_raise CompileError, ~r/unverified external Rust call/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "effects-native",
        Keyword.put(options, :roots, ["effects_native::unsupported_owned"])
      )
    end
  end
end
