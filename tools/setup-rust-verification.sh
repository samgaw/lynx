#!/bin/sh
# Install pinned extractors with Lynx's resolver, loan and result-monad fixes.
set -eu

if [ "$#" -ne 1 ]; then
  echo "usage: $0 NEW_INSTALL_DIRECTORY" >&2
  exit 1
fi
if ! command -v opam >/dev/null 2>&1; then
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
    checksum=b8ddc2f99375819a171e559aa7b14fc1e47544c9e6c8686a5261e760b65173a8 ;;
  Linux:aarch64)
    asset=aeneas-linux-aarch64.tar.gz
    checksum=ee2a9e2ada0f701c00e6c6196fa872e1ae88acce979d302e2967b450feb6a553 ;;
  Linux:x86_64)
    asset=aeneas-linux-x86_64.tar.gz
    checksum=5e076582425aa7a9b9318e419a69306d06999317d1a9fbb45fe9d751cb102579 ;;
  *) echo "no pinned Aeneas binary for this platform" >&2; exit 1 ;;
esac
mkdir -p "$1"
install_dir=$(CDPATH= cd -- "$1" && pwd)
archive="$install_dir/aeneas.tar.gz"
curl --fail --location "https://github.com/pereq-dev/aeneas/releases/download/nightly-2026.11.04-2b9e3ea/$asset" -o "$archive"
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
git -C "$install_dir" apply "$script_dir/patches/aeneas-saturating-add-spec.patch"
git -C "$install_dir" apply "$script_dir/patches/aeneas-bounded-formatting.patch"
source_dir="$install_dir/charon-source"
git clone --no-checkout --filter=blob:none https://github.com/AeneasVerif/charon "$source_dir"
git -C "$source_dir" checkout --detach 7b462d9159db2ed3015162352183906a30bfafc6
git -C "$source_dir" apply "$script_dir/patches/charon-nested-proof-roots.patch"
rustup toolchain install nightly-2026-09-17 --profile minimal \
  --component rustc-dev --component llvm-tools --component rust-src --component miri
cd "$source_dir/charon"
rustup run nightly-2026-09-17 cargo build --locked --release \
  --no-default-features --features rustc --bin charon --bin charon-driver
IN_CI=1 rustup run nightly-2026-09-17 cargo test --locked --release \
  --no-default-features --features rustc --test ui -- nested-function-proof-root
cp target/release/charon target/release/charon-driver "$install_dir/"

aeneas_source="$install_dir/aeneas-source"
git clone --no-checkout --filter=blob:none https://github.com/AeneasVerif/aeneas "$aeneas_source"
git -C "$aeneas_source" checkout --detach 2b9e3ea4662b48c19262be759dbb704f20c24364
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-static-shared-loans.patch"
git -C "$aeneas_source" apply "$script_dir/patches/aeneas-lean-result-monad.patch"
ln -s "$source_dir" "$aeneas_source/charon"
cp "$script_dir/aeneas.opam.locked" "$aeneas_source/src/aeneas.opam.locked"
# Keep compiler packages and configuration inside this installation.
opam_root="$install_dir/opam"
opam init --root="$opam_root" --bare --no-setup --yes
opam switch create --root="$opam_root" lynx-aeneas ocaml-base-compiler.5.3.0 --yes
opam install --root="$opam_root" --switch=lynx-aeneas \
  "$aeneas_source/src" --deps-only --locked --yes
aeneas_version=nightly-2026.11.04-2b9e3ea+lynx-result-monad-v1
AENEAS_VERSION="$aeneas_version" opam exec --root="$opam_root" --switch=lynx-aeneas -- \
  dune build --root "$aeneas_source/src" main.exe
cp "$aeneas_source/src/_build/default/main.exe" "$install_dir/aeneas"
printf '%s\n' "aeneas=$aeneas_version" \
  'charon=7b462d9159db2ed3015162352183906a30bfafc6+lynx-nested-proof-roots' \
  'aeneas_runtime=lynx-bounded-default-format-v2' \
  'rust=nightly-2026-09-17' > "$install_dir/lynx-toolchain"
echo "Installed. Set LYNX_AENEAS_DIR to $install_dir"
