defmodule Lynx.Rust.ContextTest do
  use ExUnit.Case

  @tools System.get_env("LYNX_AENEAS_DIR")
  @proofs Path.expand("../../fixtures/rust_workspace/proofs", __DIR__)
  @moduletag timeout: 300_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "extracts actual Cargo features and environment without copying inherited secrets", %{
    tmp_dir: tmp
  } do
    manifest = Path.join(tmp, "Cargo.toml")
    File.mkdir_p!(Path.join(tmp, "src"))

    File.write!(manifest, """
    [package]
    name = "configuration-package"
    version = "0.1.0"
    edition = "2021"
    [lib]
    name = "configuration_core"
    [features]
    special = []
    """)

    File.write!(Path.join(tmp, "src/lib.rs"), """
    pub fn selected() -> bool { cfg!(feature = "special") }
    pub fn package_name() -> &'static str { env!("CARGO_PKG_NAME") }
    const _: () = assert!(option_env!("LYNX_RECORD_FILE").is_none());
    """)

    # Build scripts keep the application's wrapper policy. Lynx selects an
    # explicit compiler driver rather than injecting a workspace wrapper.
    File.write!(Path.join(tmp, "build.rs"), """
    fn main() {
        assert!(std::env::var_os("RUSTC_WORKSPACE_WRAPPER").is_none());
        assert!(std::env::var_os("RUSTC_WRAPPER").is_none());
    }
    """)

    {output, status} =
      System.cmd("cargo", ["generate-lockfile", "--manifest-path", manifest],
        stderr_to_stdout: true
      )

    assert status == 0, output

    key = "LYNX_CONTEXT_TEST_SECRET"
    before = System.get_env(key)
    secret = "test-inherited-credential-#{System.unique_integer([:positive])}"
    System.put_env(key, secret)
    on_exit(fn -> if before, do: System.put_env(key, before), else: System.delete_env(key) end)

    context =
      Lynx.Rust.Cargo.build!(manifest, "configuration-package", Path.join(tmp, "build"),
        features: ["special"]
      )

    record = File.read!(Path.join(context.directory, "compiler.json"))
    refute record =~ secret
    assert Path.wildcard(Path.join(context.directory, "baseline-*.json")) == []
    assert context.artifact["target"]["name"] == "configuration_core"
    assert "feature=\"special\"" in context.record["arguments"]
    expanded = Lynx.Rust.Cargo.expand!(context)
    assert expanded =~ "configuration-package"
    assert expanded =~ "pub fn selected() -> bool { true }"

    # Replay must not silently change an option_env!/env! input.
    System.put_env(key, "changed")

    assert_raise RuntimeError, ~r/compiler environment changed.*LYNX_CONTEXT_TEST_SECRET/, fn ->
      Lynx.Rust.Cargo.expand!(context)
    end

    System.put_env(key, secret)

    prefix = "RustWorkspace.ConfigurationC#{System.unique_integer([:positive])}"
    model_dir = Path.join(@proofs, String.replace(prefix, ".", "/"))

    on_exit(fn ->
      File.rm_rf!(model_dir)

      for suffix <- [".llbc", ".translation.json"] do
        File.rm(Path.join(@proofs, String.replace(prefix, ".", "_") <> suffix))
      end
    end)

    extraction =
      Lynx.Rust.Extraction.run!(
        context,
        @tools,
        ["configuration_core::selected"],
        @proofs,
        prefix
      )

    assert map_size(extraction.implementations) == 1
    prove_selected!(prefix, true)

    # Same source, different Cargo feature selection: the previous property fails.
    context = Lynx.Rust.Cargo.build!(manifest, "configuration-package", Path.join(tmp, "build"))
    Lynx.Rust.Extraction.run!(context, @tools, ["configuration_core::selected"], @proofs, prefix)
    prove_selected!(prefix, false)
  end

  defp prove_selected!(prefix, expected) do
    {output, status} =
      System.cmd("lake", ["build", prefix <> ".Funs"], cd: @proofs, stderr_to_stdout: true)

    assert status == 0, output

    source = """
    module
    public import #{prefix}.Funs
    theorem selected_configuration : configuration_core.selected = Aeneas.Std.RustM.ok true := by rfl
    """

    file = %{
      "file" => "configuration-property.lean",
      "module" => prefix <> ".Property",
      "imports" => [prefix <> ".Funs"],
      "contents" => [],
      "preludes" => [
        %{
          "source" => source,
          "file" => "configuration-property.lean",
          "span" => [1],
          "indentation" => 0
        }
      ],
      "audit_modules" => [prefix <> ".Funs", prefix <> ".Property"]
    }

    [report] = Lynx.Commands.verify!(@proofs, [file])

    if expected,
      do: assert(report.status == :ok, inspect(report)),
      else: assert(report.status == :error, inspect(report))
  end
end
