#!/bin/sh
# Install the pinned upstream extractor with Lynx's nested-root resolver fix.
set -eu

if [ "$#" -ne 1 ]; then
  echo "usage: $0 NEW_INSTALL_DIRECTORY" >&2
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
printf '%s\n' 'aeneas=nightly-2026.11.04-2b9e3ea' \
  'charon=7b462d9159db2ed3015162352183906a30bfafc6+lynx-nested-proof-roots' \
  'aeneas_runtime=lynx-bounded-default-format-v1' \
  'rust=nightly-2026-09-17' > "$install_dir/lynx-toolchain"
echo "Installed. Set LYNX_AENEAS_DIR to $install_dir"
