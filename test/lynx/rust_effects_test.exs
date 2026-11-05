defmodule Lynx.Rust.EffectsTest do
  use ExUnit.Case
  @fixture Path.expand("../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for native effect extraction tests")

  @tag tmp_dir: "process-#{System.pid()}"
  test "checks the mutable transition and rejects unmodelled shared effects", %{tmp_dir: tmp} do
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Effects"))

    File.cp!(
      Path.join(@fixture, "Properties.lean"),
      Path.join(project, "Effects/Properties.lean")
    )

    packages = Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    result =
      Lynx.Rust.verify!(@fixture, "effects-core",
        roots: ["effects_core::increment"],
        tools: @tools,
        lean_project: project,
        build_dir: Path.join(tmp, "core-build"),
        module_prefix: "Effects.Extraction",
        proof_modules: ["Effects.Properties"],
        required_properties: ["Effects.Properties.increment_spec"]
      )

    assert [%{status: :ok}] = result.reports

    assert [%{rust_name: "core::num::{u64}::checked_add", implementation_verified: false}] =
             result.verification.unverified_external_calls

    context =
      Lynx.Rust.Cargo.build!(@fixture, "effects-native", Path.join(tmp, "native-build"), [])

    for root <- ["effects_native::resource_new", "effects_native::resource_increment"] do
      assert_raise CompileError, ~r/unverified external Rust call/, fn ->
        Lynx.Rust.Extraction.run!(context, @tools, [root], project, "Effects.NativeProbe")
      end
    end

    error =
      assert_raise ArgumentError, ~r/Charon reported extraction errors/, fn ->
        Lynx.Rust.Extraction.run!(
          context,
          @tools,
          ["effects_native::async_increment"],
          project,
          "Effects.AsyncProbe"
        )
      end

    assert Exception.message(error) =~ "Coroutines are not supported"
  end
end
