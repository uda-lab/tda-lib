#!/usr/bin/env bash
# Fail if any Lean source under TDA/ (or the root aggregator TDA.lean) imports the bare
# `Mathlib` root. A non-`module` file that does so maps every Mathlib module's `.olean`,
# `.olean.server` and `.olean.private` in its import closure (Issue #950, #945 finding 1):
# estimated 5.45 GiB per compiling process against a median of 1.3 GiB for a narrow importer,
# which is what makes a cold build on this container page-cache bound.
#
# Every module imports exactly the Mathlib files it uses. There is no marker to opt out:
# unlike `sorry`/custom axioms, a bare `import Mathlib` is never individually authorised —
# the fix is always to name the actual imports. Narrowing imports other than `Mathlib`
# itself (e.g. `Mathlib.Tactic`) is out of scope for this guard.
#
# A plain anchored grep is enough: `import Mathlib` followed only by optional trailing
# whitespace is never meaningful inside a string literal or a block comment opener in
# practice, and this is exactly the shape `lake`/`lean` parse as the bare root import — so no
# comment/string-stripping lexer pass is needed here, unlike the sorry/axiom guards.
#
# FAIL-CLOSED: one `grep` over all files with no error suppression under `set -euo pipefail`;
# a scanner failure aborts non-zero.
set -euo pipefail

if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check-no-bare-mathlib-import.sh" >&2
  exit 64
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

list="$(mktemp)"
trap 'rm -f "$list"' EXIT
{
  find TDA \( -path 'TDA/.agents/worktrees' -o -path 'TDA/.agents/scratch' \) -prune \
       -o -type f -name '*.lean' -print0
  [ -f TDA.lean ] && printf '%s\0' TDA.lean
} > "$list"

if [ ! -s "$list" ]; then
  echo "OK: no Lean sources to scan."
  exit 0
fi

violations="$(LC_ALL=C xargs -0 grep -nHE '^import Mathlib[[:space:]]*$' < "$list" || true)"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations" >&2
  echo "ERROR: bare 'import Mathlib' found above in TDA/ or TDA.lean." >&2
  echo "Replace it with the specific Mathlib modules the file actually uses." >&2
  exit 1
fi
echo "OK: no bare 'import Mathlib' in TDA/ or TDA.lean."
