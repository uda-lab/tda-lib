#!/usr/bin/env bash
# Thin wrapper around scripts/check_axiom_coverage.lean, the axiom-pinning coverage guard:
# every public theorem declared inside a TDA module must have a `#print axioms` line
# in scripts/print_axioms/*.lean; private theorem roots outside their dependency closures
# are audited against the same axiom allowlist. The pins are the append-only inputs used by
# scripts/check-axioms.sh. scripts/check.sh runs this immediately after that audit, under
# the same resource locks as the rest of the gate.
#
# Requires a completed `lake build` (scripts/check.sh orders this correctly). The pass/fail
# decision and the `MISSING: <name>` diagnostics are produced entirely by the Lean file
# itself (via `throwError`, which gives `lake env lean` a nonzero exit code); this wrapper
# only runs it and propagates that exit code.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

SCRIPT="scripts/check_axiom_coverage.lean"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found (install elan; see scripts/bootstrap.sh)." >&2
  exit 1
fi

echo "==> lake env lean $SCRIPT"
"$ROOT/scripts/lean.sh" lake env lean "$SCRIPT"
