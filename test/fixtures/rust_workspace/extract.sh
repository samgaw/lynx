#!/bin/sh
set -eu

fixture_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$fixture_dir/../../.." && pwd)
: "${CHARON:?Set CHARON to the pinned Aeneas release\'s charon executable}"
: "${AENEAS:?Set AENEAS to the pinned Aeneas release\'s aeneas executable}"
RUSTUP_TOOLCHAIN=$("$CHARON" toolchain-version)
export RUSTUP_TOOLCHAIN
output_dir="$fixture_dir/proofs"
mkdir -p "$output_dir"
cd "$fixture_dir/analysis"
# Charon only writes LLBC when rustc runs; force this selected root to rebuild.
cargo clean --package experiment-analysis
"$CHARON" cargo --preset=aeneas --start-from experiment_analysis::restore \
  --opaque core --opaque alloc --opaque std --include experiment_core \
  --include core::ops::control_flow::ControlFlow --include core::option::Option \
  --dest-file "$output_dir/workspace.llbc"
"$AENEAS" -backend lean -split-files -abort-on-error -warnings-as-errors \
  -dest "$output_dir" -subdir RustWorkspace/Extraction "$output_dir/workspace.llbc"
cp "$repo_dir/lean-toolchain" "$output_dir/lean-toolchain"
