#!/usr/bin/env bash
# Judge the staged challenge with the Lean comparator (Challenge and Solution are lean_lib targets of lakefile.toml).
# Usage: run-comparator.sh <project-root> <tools-dir> [config (default comparator.json)]
# Set FAKE_LANDRUN=1 for a non-sandboxed dry run (statement/axiom/kernel checks only).
set -euo pipefail
R="${1:?project root}"; T="${2:?tools dir}"; CONFIG="${3:-comparator.json}"
export HOME="${HOME:-/root}"
export PATH="$T/bin:/root/.elan/bin:$PATH"
if [ "${FAKE_LANDRUN:-0}" = "1" ]; then export COMPARATOR_LANDRUN="$T/bin/fake-landrun.sh"; fi
cd "$R"
lake build Erdos1220Challenge Erdos1220Solution
lake env comparator "$CONFIG"
