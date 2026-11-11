defmodule Lynx.Rust.SysrootTest do
  use ExUnit.Case, async: true

  test "rejects unknown sysroots before Cargo or proof preparation" do
    for {backend, package} <- [{Lynx.Rust, "core"}, {Lynx.Rustler, "nif"}] do
      assert_raise ArgumentError, "Rust sysroot must be :default or :full_mir", fn ->
        if backend == Lynx.Rust,
          do:
            backend.verify!("missing-workspace", package, roots: ["core::run"], sysroot: :unknown),
          else: backend.prepare!("missing-workspace", package, sysroot: :unknown)
      end
    end
  end

  test "full-MIR runtime extraction remains outside the qualified subset" do
    assert_raise ArgumentError, "full-MIR sysroot currently requires pure execution", fn ->
      Lynx.Rust.verify!("missing-workspace", "core",
        roots: ["core::run"],
        sysroot: :full_mir,
        execution: :runtime
      )
    end
  end

  test "Charon receives a managed sysroot once while direct replay keeps it" do
    arguments = [
      "--crate-name",
      "sample",
      "--sysroot",
      "/full-mir",
      "--emit=metadata",
      "sample.rs"
    ]

    record = %{"arguments" => arguments}
    context = %{record: record, sysroot: %{path: "/full-mir"}}

    expected = [
      "--crate-name",
      "sample",
      "sample.rs",
      "--crate-type=rlib",
      "--emit=metadata",
      "--out-dir",
      Path.expand("output")
    ]

    assert Lynx.Rust.Cargo.extraction_arguments(context, "output") == expected
    assert context.record["arguments"] == arguments
    unmanaged = %{context | sysroot: nil}
    assert "--sysroot" in Lynx.Rust.Cargo.extraction_arguments(unmanaged, "output")
  end

  test "full-MIR target files remain outside the supported configuration" do
    assert_raise ArgumentError,
                 "full-MIR extraction requires a named Rust target, not a target file",
                 fn ->
                   Lynx.Rust.Sysroot.cargo_options!(
                     [sysroot: :full_mir, cargo: [target: "targets/custom.json"]],
                     "."
                   )
                 end
  end
end
