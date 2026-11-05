# From the Lynx repository root, with Lean 4.35.0 and the pinned tools installed:
#   tools/setup-rust-verification.sh /absolute/tool-directory
#   LYNX_AENEAS_DIR=/absolute/tool-directory mix run examples/rust_workspace/run.exs
# Add LYNX_CACHE=0 LYNX_DEBUG=lean to inspect uncached verification.
#
# This directory contains every example implementation and property. Generated
# Cargo/Lean artifacts stay in ignored directories. No test fixture is required.
# Proofs cover the extracted Rust bodies, modelled Rustler adapter and Elixir
# laws. Compilation/translation, native FFI, allocation and machine-code execution
# remain trusted boundaries. Resources, locking and async are not verified here.

ExUnit.start()
Code.require_file("setup.exs", __DIR__)
prepared = Lynx.Rustler.prepare!(LynxWorkspaceExample.options())
LynxWorkspaceExample.load_native!(prepared.library)
Code.require_file("laws.exs", __DIR__)
