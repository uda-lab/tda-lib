#!/usr/bin/env bash
# Canonical local/CI integrity gate, in this order:
#   textual guards (sorry/admit, custom axioms, transient artefacts, imports-only root
#   aggregator) → lake build →
#   live axiom audit → axiom-coverage guard (every public theorem is pinned in
#   scripts/print_axioms.lean).
# The whole run is serialised container-wide on /tmp/lean-build.lock (scripts/lib/build-lock.sh
# holds it on fd 9 for the lifetime of this process and every child): concurrent mathlib
# builds in a shared container OOM each other. A killed run releases the lock with its
# descriptor — nothing stale to reclaim.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

. "$ROOT/scripts/lib/build-lock.sh"

step() { echo "==> $*"; }

if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != "--stable" ]; }; then
  echo "usage: scripts/check.sh [--stable]" >&2; exit 64
fi
stable=0
if [ "${1:-}" = --stable ] || [ "${TDA_STABLE_RELEASE:-0}" = 1 ] || [ "$(git branch --show-current)" = main ]; then stable=1; fi
step "sorry/admit and custom axiom policy"
if [ "$stable" = 1 ]; then
  bash scripts/check-no-sorry.sh --stable
  bash scripts/check-no-custom-axiom.sh --stable
else
  bash scripts/check-no-sorry.sh
  bash scripts/check-no-custom-axiom.sh
fi
step "no transient artefacts tracked"; bash scripts/check-transient-artifacts.sh
step "root aggregator imports-only";   bash scripts/check-root-aggregator.sh

# From here only lake runs. Inside a linked git worktree the caller's GIT_DIR & co. would make
# lake's git subprocesses inside .lake/packages/* resolve THIS repository instead of their own;
# clear them now (not earlier: the transient guard above needs the caller's git object access).
# shellcheck disable=SC2046
unset $(git rev-parse --local-env-vars)

step "lake build";                     lake build
step "live axiom audit";               bash scripts/check-axioms.sh
step "axiom coverage";                 bash scripts/check-axiom-coverage.sh
echo "CHECK OK"
