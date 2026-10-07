#!/usr/bin/env bash
# Fail if an unmarked `sorry` (or `admit`, which is `sorry` under another name)
# appears in *code* in Lean sources.
#
# A `sorry` is permitted only when its OWN line carries a marker citing the Issue
# that explicitly authorises the work to land incomplete:
#     theorem foo : P := by sorry  -- ALLOW_SORRY: #<n> <reason>
#
# Per-line markers with an Issue number are deliberate: every incomplete proof is
# justified in place and traceable, so `sorry` cannot accumulate silently. A marked
# `sorry` still fails scripts/check-axioms.sh if it reaches a pinned theorem.
#
# Only a `sorry` token in actual code counts. Comments and string literals are
# stripped by the shared lexer scripts/lean-code-scan.awk before matching, so the
# word may appear freely in docstrings and strings; the ALLOW_SORRY marker, which
# lives in the trailing line comment, is still honoured on real code lines.
#
# FAIL-CLOSED by design: one `awk` over all files with NO error suppression under
# `set -euo pipefail`, so a scanner or portability failure aborts non-zero.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Enumerate Lean sources fail-closed: `find` writes to a temp file and its exit
# status is checked BEFORE the list is consumed (a bare process substitution would
# swallow traversal errors and let a partial scan report OK). `.git`/`.lake` are
# pruned by basename at any depth; agent worktrees under .claude/worktrees/ are
# scanned by their own CI; .claude/scratch/ is the designated (gitignored) home of
# proof experiments and is never a source.
list="$(mktemp)"
trap 'rm -f "$list"' EXIT
find . \( -name '.git' -o -name '.lake' -o -path './.claude/worktrees' -o -path './.claude/scratch' \) -prune \
     -o -type f -name '*.lean' -print0 > "$list"

if [ ! -s "$list" ]; then
  echo "OK: no Lean sources to scan."
  exit 0
fi

# NUL-safe xargs batching keeps the scan under ARG_MAX regardless of tree size; a
# failing awk in any batch makes the substitution non-zero under `pipefail`.
violations="$(xargs -0 awk -v mode=sorry -f scripts/lean-code-scan.awk < "$list")"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations" >&2
  echo "ERROR: unmarked 'sorry'/'admit' found above." >&2
  echo "Add '-- ALLOW_SORRY: #<issue> <reason>' on the same line (only for work an Issue explicitly authorises to land incomplete), or finish the proof." >&2
  exit 1
fi
echo "OK: no unmarked 'sorry'/'admit' in Lean sources."
