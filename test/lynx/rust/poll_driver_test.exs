defmodule Lynx.Rust.PollDriverTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "safe-pin-new-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned safe-pin-new backend")

  @tag :tmp_dir
  test "proves actual Rust caller polling and cancellation across a first-party Future", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Driver"))
    property = Path.join(project, "Driver/Properties.lean")
    original = File.read!(Path.join(@fixture, "NativePollDriver.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::drive_paused_counter"],
      futures: :polling,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      module_prefix: "Driver.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Driver.Properties"],
      required_properties:
        Enum.map(
          ~w(callee_pending callee_ready driver_contract driver_next completion cancellation missing_callback),
          &("Driver.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.implementations,
             &(&1.rust_name == "effects_native::drive_paused_counter")
           )

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))
    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "driver.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom driverTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    false_property =
      String.replace(
        original,
        "(.ok (none, context), NativeWaker.notifiedEnv context.waker env)",
        "(.ok (some value, context), NativeWaker.notifiedEnv context.waker env)"
      )

    refute false_property == original
    File.write!(property, false_property)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)
    source = Path.join(workspace, "native/src/lib.rs")
    rust = File.read!(source)

    changed =
      String.replace(rust, "Poll::Ready(value) => Some(value),", "Poll::Ready(_value) => None,")

    refute changed == rust
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end

  @tag :tmp_dir
  test "rejects direct unsafe pin helper calls", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    source = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      source,
      "#![feature(pin_macro_internals)]\n" <>
        File.read!(source) <>
        """

        pub fn macro_driver(resource: rustler::ResourceArc<CounterResource>, amount: u64,
            context: &mut std::task::Context<'_>) -> std::task::Poll<bool> {
            use std::future::Future;
            let mut storage = std::pin::PinMacroHelper { value: resource_suspending(resource, amount) };
            let future = unsafe { std::pin::pin_new_unchecked_in_helper(&mut storage) };
            future.poll(context)
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
                 ~r/unverified external Rust call core::pin::pin_new_unchecked_in_helper/,
                 fn ->
                   Lynx.Rust.verify!(workspace, "effects-native",
                     roots: ["effects_native::macro_driver"],
                     futures: :cancelling,
                     execution: :runtime,
                     owned_drops: true,
                     tools: @tools,
                     lean_project: project,
                     build_dir: Path.join(tmp, "build"),
                     module_prefix: "Rejected.Extraction"
                   )
                 end
  end
end
