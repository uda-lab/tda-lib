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
# Uses the shared lexer's `mode=imports` (scripts/lean-code-scan.awk), which already strips
# comments and string literals and handles `module`/`public`/`meta`/`all` modifiers and `«…»`
# escapes, emitting one resolved module name per import. A plain line-anchored grep was tried
# first and rejected: `import Mathlib -- needed for tactics` still loads all of Mathlib but
# does not match a pattern requiring only trailing whitespace after `Mathlib`, so a trailing
# comment would silently defeat the guard. Checking the lexer's output for an exact `Mathlib`
# line (not `Mathlib.Sub`, which is a legitimate narrow import) avoids that gap and also
# avoids the opposite mistake of flagging `import Mathlib` text that only appears inside a
# comment.
#
# FAIL-CLOSED: `set -euo pipefail` with no command run inside a conditional that would
# swallow a nonzero exit, so a lexer failure (unreadable file, scanner bug) aborts the whole
# script non-zero instead of silently reporting success.
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

violations=""
while IFS= read -r -d '' file; do
  modules="$(LC_ALL=C awk -v mode=imports -f "$ROOT/scripts/lean-code-scan.awk" "$file")"
  if printf '%s\n' "$modules" | grep -qxF 'Mathlib'; then
    violations="$violations$file: bare 'import Mathlib'
"
  fi
done < "$list"

if [ -n "$violations" ]; then
  printf '%s' "$violations" >&2
  echo "ERROR: bare 'import Mathlib' found above in TDA/ or TDA.lean." >&2
  echo "Replace it with the specific Mathlib modules the file actually uses." >&2
  exit 1
fi
echo "OK: no bare 'import Mathlib' in TDA/ or TDA.lean."
