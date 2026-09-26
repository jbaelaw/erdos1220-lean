#!/usr/bin/env bash
# Install landrun (sandbox), lean4export, comparator for judging Challenge vs Solution.
# Adapted from elliotglazer/erdos501 scripts/install-comparator-tools.sh (Apache-2.0), same pins;
# additionally bootstraps a private Go toolchain when `go` is absent (no system-wide install).
#
# Usage: install-comparator-tools.sh <tools-dir> [toolchain]   (toolchain default v4.35.0-rc3, the project toolchain)
set -euo pipefail
TOOLS="${1:?tools dir}"
LEAN_TAG="${2:-v4.35.0-rc3}"
TOOLCHAIN="leanprover/lean4:$LEAN_TAG"
mkdir -p "$TOOLS/bin"
export HOME="${HOME:-/root}"
export GOCACHE="${GOCACHE:-$TOOLS/gocache}"
export PATH="$TOOLS/bin:$TOOLS/go/bin:/root/.elan/bin:$PATH"

COMPARATOR_REV="${COMPARATOR_REV:-777e7f56119efc0fac34003db4efe831e0b53723}"
LEAN4EXPORT_REV="${LEAN4EXPORT_REV:-$LEAN_TAG}"
LANDRUN_REV="${LANDRUN_REV:-5ed4a3db3a4ad930d577215c6b9abaa19df7f99f}"
GO_VERSION="${GO_VERSION:-1.22.12}"

if ! command -v go >/dev/null; then
  echo "== bootstrapping Go $GO_VERSION into $TOOLS/go"
  curl -fsSL "https://go.dev/dl/go${GO_VERSION}.linux-amd64.tar.gz" -o "$TOOLS/go.tgz"
  tar -C "$TOOLS" -xzf "$TOOLS/go.tgz"
  rm -f "$TOOLS/go.tgz"
fi
echo "== landrun @ $LANDRUN_REV"
GOPATH="$TOOLS/gopath" GOBIN="$TOOLS/bin" go install "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_REV"

echo "== lean4export @ $LEAN4EXPORT_REV (built with $TOOLCHAIN)"
[ -d "$TOOLS/lean4export" ] || git clone -q https://github.com/leanprover/lean4export.git "$TOOLS/lean4export"
( cd "$TOOLS/lean4export"
  git fetch -q --tags
  git checkout -q "$LEAN4EXPORT_REV"
  echo "$TOOLCHAIN" > lean-toolchain
  lake build lean4export
  ln -sf "$PWD/.lake/build/bin/lean4export" "$TOOLS/bin/lean4export" )

echo "== comparator @ $COMPARATOR_REV"
[ -d "$TOOLS/comparator" ] || git clone -q https://github.com/leanprover/comparator.git "$TOOLS/comparator"
( cd "$TOOLS/comparator"
  git fetch -q
  git checkout -q "$COMPARATOR_REV"
  # build comparator with the project toolchain so that its embedded kernel matches the export
  echo "$TOOLCHAIN" > lean-toolchain
  lake build comparator
  ln -sf "$PWD/.lake/build/bin/comparator" "$TOOLS/bin/comparator"
  cp scripts/fake-landrun.sh "$TOOLS/bin/fake-landrun.sh" 2>/dev/null || true )

echo "== versions"
landrun --version 2>&1 | head -1 || true
ls -la "$TOOLS/bin"
echo INSTALL_DONE
