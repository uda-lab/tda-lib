#!/usr/bin/env bash
# Canonical local/CI integrity gate, in this order:
#   textual guards (sorry/admit, custom axioms, transient artefacts, merge-conflict markers,
#   imports-only root/area aggregator, no bare `import Mathlib`) → lake build →
#   live axiom audit → axiom-coverage guard (every public theorem is pinned in
#   scripts/print_axioms/*.lean; uncovered private theorem roots obey the same allowlist) →
#   Comparator agreement for the frozen bounded-pilot contract
#   (docs/adr/0003-comparator-pilot-contract.md; measured ≤ 60s on this container).
# The whole gate holds canonical build/dependency path locks across its nested wrappers.
# Independent workspaces may proceed when resources permit; shared mutable paths exclude.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

# scripts/check-comparator.sh honours TDA_COMPARATOR_SKIP_SANDBOXED_RUN unconditionally; it
# is Issue #951's incremental gate's own opt-in hit-path signal, set inline only on that
# gate's own hit-path call site. An ambiently leaked value here — the plain/--stable full
# gate this script runs below — would silently skip the sandboxed Comparator run this gate
# is supposed to be authoritative for, print "CHECK OK" regardless, and (via the incremental
# gate's own full-mode record refresh) write a Comparator PASS record every other worktree's
# incremental gate would then also trust.
unset TDA_COMPARATOR_SKIP_SANDBOXED_RUN

. "$ROOT/scripts/lib/build-lock.sh"

step() { echo "==> $*"; }

if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != "--stable" ] && [ "$1" != "--incremental" ]; }; then
  echo "usage: scripts/check.sh [--stable|--incremental]" >&2; exit 64
fi
incremental=0
if [ "${1:-}" = --incremental ]; then incremental=1; fi
stable=0
if [ "${1:-}" = --stable ] || [ "${TDA_STABLE_RELEASE:-0}" = 1 ] || [ "$(git branch --show-current)" = main ]; then stable=1; fi
if [ "$incremental" = 1 ] && [ "$stable" = 1 ]; then
  echo "ERROR: --incremental and --stable (including TDA_STABLE_RELEASE=1 or the main branch) are mutually exclusive." >&2
  exit 64
fi
step "sorry/admit and custom axiom policy"
if [ "$stable" = 1 ]; then
  bash scripts/check-no-sorry.sh --stable
  bash scripts/check-no-custom-axiom.sh --stable
else
  bash scripts/check-no-sorry.sh
  bash scripts/check-no-custom-axiom.sh
fi
step "no transient artefacts tracked"; bash scripts/check-transient-artifacts.sh
step "no merge-conflict markers tracked"; bash scripts/check-conflict-markers.sh
step "no bare 'import Mathlib'"; bash scripts/check-no-bare-mathlib-import.sh
step "root/area aggregators imports-only"; bash scripts/check-root-aggregator.sh

# From here only lake runs. Inside a linked git worktree the caller's GIT_DIR & co. would make
# lake's git subprocesses inside .lake/packages/* resolve THIS repository instead of their own;
# clear them now (not earlier: the transient guard above needs the caller's git object access).
# shellcheck disable=SC2046
unset $(git rev-parse --local-env-vars)

if [ "$incremental" = 1 ]; then
  # From here on, scripts/check-incremental.sh (Issue #951) is the local pre-PR gate: it
  # re-runs `lake build` and selectively re-audits axioms/coverage/Comparator, falling back
  # to the unchanged full gate below whenever eligibility cannot be established. Its own exit
  # code is this script's exit code; its final line never reads `CHECK OK`. It runs with the
  # same cleared git env-vars as the rest of this gate, for the same reason.
  bash "$ROOT/scripts/check-incremental.sh"
  exit $?
fi

step "lake build";                     "$ROOT/scripts/lean.sh" lake build
step "live axiom audit";               bash scripts/check-axioms.sh
# Advisory pin diagnostics (PIN TYPE/DOC ADVISORY) compare against the integration merge base;
# never fatal. An explicit TDA_PIN_ADVISORY_BASE (also empty, as the pre-push hook may pass) wins.
if [ -z "${TDA_PIN_ADVISORY_BASE+x}" ]; then
  integration=origin/develop
  git rev-parse --verify --quiet "$integration" >/dev/null || integration=origin/main
  TDA_PIN_ADVISORY_BASE="$(git merge-base HEAD "$integration" 2>/dev/null || true)"
  export TDA_PIN_ADVISORY_BASE
fi
step "axiom coverage";                 bash scripts/check-axiom-coverage.sh
step "Comparator agreement (bounded pilot)"; bash scripts/check-comparator.sh
echo "CHECK OK"
