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
# Use the same checked schema normalization as the normal extraction workflow.
cd "$repo_dir"
LYNX_EXPERIMENT_LLBC="$output_dir/workspace.llbc" mix run -e '
  path = System.fetch_env!("LYNX_EXPERIMENT_LLBC")
  document = path |> File.read!() |> JSON.decode!()
  {document, _queries} = Lynx.Rust.LLBCJson.drop_query_metadata!(document)
  File.write!(Path.rootname(path) <> ".aeneas.llbc", Lynx.Rust.LLBCJson.encode_like!(document, path))
'
"$AENEAS" -backend lean -split-files -abort-on-error -warnings-as-errors \
  -dest "$output_dir" -subdir RustWorkspace/Extraction "$output_dir/workspace.aeneas.llbc"
cp "$repo_dir/lean-toolchain" "$output_dir/lean-toolchain"
