#!/usr/bin/env bash
# Fail on undeclared trust-extending declarations in Lean sources:
#     axiom   constant   opaque   unsafe
#
# These widen the trusted base or hide content behind an irreducible term. They
# are permitted only when the declaration line carries a marker citing the Issue
# in which the owner authorised them:
#     axiom foo : ...  -- ALLOW_AXIOM: #<n> <reason>
# Even then, scripts/check-axioms.sh rejects any pinned theorem whose closure
# contains a project axiom; the marker only silences this textual guard.
#
# Matching is anchored to declaration-leading keywords (optionally preceded by
# attributes/modifiers) in the code of each line after the shared lexer
# scripts/lean-code-scan.awk has removed comments and string literals, so the
# words inside docstrings, strings or identifiers do not trip the check.
#
# FAIL-CLOSED: one `awk` over all files with no error suppression under
# `set -euo pipefail`; a scanner failure aborts non-zero.
set -euo pipefail

if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != "--stable" ]; }; then
  echo "usage: scripts/check-no-custom-axiom.sh [--stable]" >&2; exit 64
fi
mode=axiom
if [ "${1:-}" = --stable ]; then mode=stable_axiom; fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

list="$(mktemp)"
trap 'rm -f "$list"' EXIT
find . \( -name '.git' -o -name '.lake' -o -path './.agents/worktrees' -o -path './.agents/scratch' -o -path './.claude/worktrees' -o -path './.claude/scratch' \) -prune \
     -o -type f -name '*.lean' -print0 > "$list"

if [ ! -s "$list" ]; then
  echo "OK: no Lean sources to scan."
  exit 0
fi

violations="$(xargs -0 awk -v mode="$mode" -f scripts/lean-code-scan.awk < "$list")"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations"
  echo "ERROR: undeclared axiom/constant/opaque/unsafe found above." >&2
  echo "Add '-- ALLOW_AXIOM: #<issue> <reason>' on the same line; this needs an owner-authorised Issue, and scripts/check-axioms.sh still rejects it if it reaches a pinned theorem." >&2
  exit 1
fi
echo "OK: no undeclared axiom/constant/opaque/unsafe in Lean sources."
