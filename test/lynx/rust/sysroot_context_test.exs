defmodule Lynx.Rust.SysrootContextTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 120_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for compiler-context checks")

  @tag :tmp_dir
  test "native and full-MIR builds give host macros the same Rust flags", %{tmp_dir: tmp} do
    for name <- ~w(macros consumer), do: File.mkdir_p!(Path.join([tmp, name, "src"]))

    File.write!(Path.join(tmp, "Cargo.toml"), """
    [workspace]
    members = ["macros", "consumer"]
    resolver = "2"
    """)

    File.write!(Path.join(tmp, "macros/Cargo.toml"), """
    [package]
    name = "flags-macros"
    version = "0.1.0"
    edition = "2021"
    [lib]
    proc-macro = true
    [lints.rust]
    unexpected_cfgs = { level = "warn", check-cfg = ['cfg(lynx_host_flag)'] }
    """)

    File.write!(Path.join(tmp, "macros/src/lib.rs"), """
    extern crate proc_macro;
    #[proc_macro]
    pub fn flag(_input: proc_macro::TokenStream) -> proc_macro::TokenStream {
        cfg!(lynx_host_flag)
            .to_string()
            .parse()
            .expect("boolean literal")
    }
    """)

    File.write!(Path.join(tmp, "consumer/Cargo.toml"), """
    [package]
    name = "flags-consumer"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    flags-macros = { path = "../macros" }
    """)

    File.write!(
      Path.join(tmp, "consumer/src/lib.rs"),
      "pub const FLAG: bool = flags_macros::flag!();\n"
    )

    {_, 0} =
      System.cmd("rustup", [
        "run",
        "nightly-2026-09-17",
        "cargo",
        "generate-lockfile",
        "--manifest-path",
        Path.join(tmp, "Cargo.toml")
      ])

    previous = System.get_env("RUSTFLAGS")
    previous_encoded = System.get_env("CARGO_ENCODED_RUSTFLAGS")

    on_exit(fn ->
      if previous, do: System.put_env("RUSTFLAGS", previous), else: System.delete_env("RUSTFLAGS")

      if previous_encoded,
        do: System.put_env("CARGO_ENCODED_RUSTFLAGS", previous_encoded),
        else: System.delete_env("CARGO_ENCODED_RUSTFLAGS")
    end)

    System.delete_env("CARGO_ENCODED_RUSTFLAGS")
    System.put_env("RUSTFLAGS", "--cfg lynx_host_flag")
    build = Path.join(tmp, "build")
    options = [sysroot: :full_mir]
    implicit = Lynx.Rust.Cargo.build!(tmp, "flags-consumer", build)
    assert Lynx.Rust.Cargo.expand!(implicit) =~ "pub const FLAG: bool = true;"

    assert_raise ArgumentError,
                 "full-MIR extraction requires the same explicit native Cargo target",
                 fn ->
                   Lynx.Rust.Sysroot.context!(
                     implicit,
                     tmp,
                     "flags-consumer",
                     build,
                     @tools,
                     options
                   )
                 end

    native =
      Lynx.Rust.Cargo.build!(
        tmp,
        "flags-consumer",
        build,
        Lynx.Rust.Sysroot.cargo_options!(options, tmp)
      )

    metadata = Lynx.Rust.Sysroot.context!(native, tmp, "flags-consumer", build, @tools, options)
    expanded = Lynx.Rust.Cargo.expand!(native)
    assert expanded =~ "pub const FLAG: bool = false;"
    assert Lynx.Rust.Cargo.expand!(metadata) == expanded
  end

  @tag :tmp_dir
  test "resolves Cargo configured targets without overriding them with the host", %{tmp_dir: tmp} do
    File.mkdir_p!(Path.join(tmp, ".cargo"))
    config = Path.join(tmp, ".cargo/config.toml")
    File.write!(config, "[build]\ntarget = \"x86_64-unknown-linux-gnu\"\n")
    previous = System.get_env("CARGO_BUILD_TARGET")

    on_exit(fn ->
      if previous,
        do: System.put_env("CARGO_BUILD_TARGET", previous),
        else: System.delete_env("CARGO_BUILD_TARGET")
    end)

    System.delete_env("CARGO_BUILD_TARGET")

    assert [target: "x86_64-unknown-linux-gnu"] =
             Lynx.Rust.Sysroot.cargo_options!([sysroot: :full_mir], tmp)

    System.put_env("CARGO_BUILD_TARGET", "aarch64-apple-darwin")

    assert [target: "aarch64-apple-darwin"] =
             Lynx.Rust.Sysroot.cargo_options!([sysroot: :full_mir], tmp)

    assert [target: "x86_64-unknown-freebsd"] =
             Lynx.Rust.Sysroot.cargo_options!(
               [sysroot: :full_mir, cargo: [target: "x86_64-unknown-freebsd"]],
               tmp
             )

    System.delete_env("CARGO_BUILD_TARGET")

    File.write!(
      config,
      "[build]\ntarget = [\"x86_64-unknown-linux-gnu\", \"aarch64-apple-darwin\"]\n"
    )

    assert_raise ArgumentError, "Rust verification requires a single Cargo target", fn ->
      Lynx.Rust.Sysroot.cargo_options!([sysroot: :full_mir], tmp)
    end
  end
end
