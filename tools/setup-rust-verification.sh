#!/bin/sh
# Install pinned extractors; --runtime opts into the patched native runtime stack.
set -eu

verification_profile=pure
case "${1-}" in
  --pure) shift ;;
  --unpatched) verification_profile=unpatched; shift ;;
  --runtime) verification_profile=runtime; shift ;;
  -*) echo "usage: $0 [--pure|--unpatched|--runtime] NEW_INSTALL_DIRECTORY" >&2; exit 1 ;;
esac
if [ "$#" -ne 1 ]; then
  echo "usage: $0 [--pure|--unpatched|--runtime] NEW_INSTALL_DIRECTORY" >&2
  exit 1
fi
if [ "$verification_profile" = runtime ] && ! command -v opam >/dev/null 2>&1; then
  echo "opam is required to build the patched Aeneas extractor" >&2
  exit 1
fi
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ -e "$1" ]; then
  echo "installation directory already exists: $1" >&2
  exit 1
fi
case "$(uname -s):$(uname -m)" in
  Darwin:arm64)
    asset=aeneas-macos-aarch64.tar.gz
    checksum=b8ddc2f99375819a171e559aa7b14fc1e47544c9e6c8686a5261e760b65173a8
    pure_checksum=0d71e3d81d3eeaa573d48876e412811a0a01f25bfc9bc0966ea1ab65c74fd287 ;;
  Linux:aarch64)
    asset=aeneas-linux-aarch64.tar.gz
    checksum=ee2a9e2ada0f701c00e6c6196fa872e1ae88acce979d302e2967b450feb6a553
    pure_checksum=4af73179259ab5eb5c3a265572c3be0e9aba2ced09b1500e343d1b71defac49a ;;
  Linux:x86_64)
    asset=aeneas-linux-x86_64.tar.gz
    checksum=5e076582425aa7a9b9318e419a69306d06999317d1a9fbb45fe9d751cb102579
    pure_checksum=139d05e5ffa25e0a08906d68134fb8144794d6f32e6d7729a5bf93419d4c6985 ;;
  *) echo "no pinned Aeneas binary for this platform" >&2; exit 1 ;;
esac
release_tag=nightly-2026.11.04-2b9e3ea
if [ "$verification_profile" != runtime ]; then
  release_tag=build-2b9e3ea
  checksum=$pure_checksum
fi
mkdir -p "$1"
install_dir=$(CDPATH= cd -- "$1" && pwd)
archive="$install_dir/aeneas.tar.gz"
curl --fail --location "https://github.com/pereq-dev/aeneas/releases/download/$release_tag/$asset" -o "$archive"
if command -v sha256sum >/dev/null; then
  actual=$(sha256sum "$archive" | cut -d ' ' -f 1)
else
  actual=$(shasum -a 256 "$archive" | cut -d ' ' -f 1)
fi
if [ "$actual" != "$checksum" ]; then
  echo "Aeneas archive checksum mismatch" >&2
  exit 1
fi
tar -xzf "$archive" -C "$install_dir"
rustup toolchain install nightly-2026-09-17 --profile minimal \
  --component rustc-dev --component llvm-tools --component rust-src --component miri
if [ "$verification_profile" = unpatched ]; then
  printf '%s\n' 'profile=unpatched' 'aeneas=build-2b9e3ea' \
    'charon=build-2b9e3ea-release' 'rust=nightly-2026-09-17' > "$install_dir/lynx-toolchain"
  echo "Installed release binaries without Lynx patches. Set LYNX_AENEAS_DIR to $install_dir"
  echo "Nested NIF roots require root_attribute selection and annotated Rust functions."
  exit 0
fi
source_dir="$install_dir/charon-source"
git clone --no-checkout --filter=blob:none https://github.com/AeneasVerif/charon "$source_dir"
git -C "$source_dir" checkout --detach 7b462d9159db2ed3015162352183906a30bfafc6
git -C "$source_dir" apply "$script_dir/patches/charon-nested-proof-roots.patch"
if [ "$verification_profile" = runtime ]; then
  git -C "$source_dir" apply "$script_dir/patches/charon-needs-drop.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-immediate-futures.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-pin-borrow-transfer.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-suspending-futures.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-cancelling-futures.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-owned-drops.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-owned-future-captures.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-safe-pin-new.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-pin-macro.patch"
  git -C "$source_dir" apply "$script_dir/patches/charon-pin-as-mut.patch"
fi
cd "$source_dir/charon"
rustup run nightly-2026-09-17 cargo build --locked --release \
  --no-default-features --features rustc --bin charon --bin charon-driver
IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
  --no-default-features --features rustc --test ui -- nested-function-proof-root
if [ "$verification_profile" = runtime ]; then
  IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
    --no-default-features --features rustc --test crate_data -- needs_drop
  IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
    --no-default-features --features rustc --test crate_data -- immediate_future_state_machine
  IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
    --no-default-features --features rustc --test crate_data -- pin_get_mut_transfers_only_the_standard_wrapper
  IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
    --no-default-features --features rustc --test crate_data -- owned_drop_entry_retains_compiler_field_cleanup
  IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
    --no-default-features --features rustc --test crate_data -- owned_future_capture_uses_initial_slot_and_compiler_drop
  IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
    --no-default-features --features rustc --test crate_data -- safe_pin_new_inlines_only_the_checked_standard_constructor
  IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
    --no-default-features --features rustc --test crate_data -- pin_macro_links_actual_coroutine_poll_and_structural_drop
  IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
    --no-default-features --features rustc --test crate_data -- pin_as_mut_reborrows_only_standard_mutable_references
fi
cp target/release/charon target/release/charon-driver "$install_dir/"
if [ "$verification_profile" = pure ]; then
  printf '%s\n' 'profile=pure' 'aeneas=build-2b9e3ea' \
    'charon=7b462d9159db2ed3015162352183906a30bfafc6+lynx-nested-proof-roots' \
    'rust=nightly-2026-09-17' > "$install_dir/lynx-toolchain"
  echo "Installed pure toolchain. Set LYNX_AENEAS_DIR to $install_dir"
  exit 0
fi

aeneas_source="$install_dir/aeneas-source"
git clone --no-checkout --filter=blob:none https://github.com/AeneasVerif/aeneas "$aeneas_source"
git -C "$aeneas_source" checkout --detach 2b9e3ea4662b48c19262be759dbb704f20c24364
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-static-shared-loans.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-lean-result-monad.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-assertion-unwind-input.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-external-global-names.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-immediate-futures.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-workspace-roots.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-undefined-behavior.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-lean-back-projections.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-native-loops.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-effectful-calls.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-partial-discriminants.patch"
ln -s "$source_dir" "$aeneas_source/charon"
cp "$script_dir/aeneas.opam.locked" "$aeneas_source/src/aeneas.opam.locked"
# Keep compiler packages and configuration inside this installation.
opam_root="$install_dir/opam"
opam init --root="$opam_root" --bare --no-setup --yes
opam switch create --root="$opam_root" lynx-aeneas ocaml-base-compiler.5.3.0 --yes
opam install --root="$opam_root" --switch=lynx-aeneas \
  "$aeneas_source/src" --deps-only --locked --yes
aeneas_version=nightly-2026.11.04-2b9e3ea+lynx-result-monad-v1+assertion-unwind-v1+global-names-v1+immediate-futures-v1+workspace-roots-v1+undefined-behavior-v1+native-loops-v1+effectful-calls-v1+partial-discriminants-v1
AENEAS_VERSION="$aeneas_version" opam exec --root="$opam_root" --switch=lynx-aeneas -- \
  dune build --root "$aeneas_source/src" main.exe
cp "$aeneas_source/src/_build/default/main.exe" "$install_dir/aeneas"
printf '%s\n' 'profile=runtime' "aeneas=$aeneas_version" \
  'charon=7b462d9159db2ed3015162352183906a30bfafc6+lynx-nested-proof-roots+needs-drop-v1+pin-borrow-transfer-v1+immediate-futures-v1+suspending-futures-v1+cancelling-futures-v1+owned-drops-v1+owned-captures-v1+safe-pin-new-v1+pin-macro-v1+pin-as-mut-v1' \
  'aeneas_lean=tuple-back-projections-v1' \
  'aeneas_loops=native-loops-v1' \
  'aeneas_effects=effectful-calls-v1' \
  'aeneas_discriminants=partial-discriminants-v1' \
  'rust=nightly-2026-09-17' > "$install_dir/lynx-toolchain"
echo "Installed. Set LYNX_AENEAS_DIR to $install_dir"
