#!/usr/bin/env bash
# Install a private Rust toolchain (rustup; RUSTUP_HOME/CARGO_HOME inside <tools-dir>, nothing
# system-wide) and build nanoda_bin for the comparator's `enable_nanoda` check.
# Pin: robsimmons/nanoda_lib 68d5ca9 — the pin used by leanprover/lean-eval and by
# elliotglazer/erdos501's install-comparator-tools.sh (upstream: ammkrn/nanoda_lib).
# Usage: install-nanoda.sh <tools-dir>
set -euo pipefail
TOOLS="${1:?tools dir}"
export HOME="${HOME:-/root}"
export RUSTUP_HOME="$TOOLS/rustup" CARGO_HOME="$TOOLS/cargo"
NANODA_REPO="${NANODA_REPO:-https://github.com/robsimmons/nanoda_lib.git}"
NANODA_REV="${NANODA_REV:-68d5ca9db226849b41a6fff59d796ff19d0a8840}"
mkdir -p "$TOOLS/bin"
if [ ! -x "$CARGO_HOME/bin/cargo" ]; then
  curl -fsSL https://sh.rustup.rs -o "$TOOLS/rustup-init.sh"
  sh "$TOOLS/rustup-init.sh" -y --no-modify-path --profile minimal --default-toolchain stable
fi
export PATH="$CARGO_HOME/bin:$PATH"
cargo --version
[ -d "$TOOLS/nanoda_lib" ] || git clone -q "$NANODA_REPO" "$TOOLS/nanoda_lib"
cd "$TOOLS/nanoda_lib"
git fetch -q
git checkout -q "$NANODA_REV"
git log -1 --format='nanoda_lib %H %cd'
cargo build --release
ln -sf "$PWD/target/release/nanoda_bin" "$TOOLS/bin/nanoda_bin"
ls -la "$TOOLS/bin/nanoda_bin"
echo NANODA_DONE
