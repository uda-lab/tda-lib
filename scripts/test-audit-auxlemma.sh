#!/usr/bin/env bash
# Real regression for the `linter.auxLemma` suppression added to the generated combined
# audit file (#949). Printing thousands of `#print axioms` lines in one Lean process
# surfaces that linter for any pin that intentionally names an auto-generated `._proof_1`
# declaration; its warning has no record terminator and was getting glued onto the
# preceding record, so the audit flagged it "malformed" — a real 3-declaration failure,
# not a hypothetical (see the commit that added `set_option linter.auxLemma false`).
#
# This proves the project's existing `._proof_1`-pinned declarations are genuinely
# audited, not silently skipped, now that the linter is suppressed. It needs the real
# library and a completed `lake build`: the fixture harness `test-private-axioms.sh`
# uses elsewhere in this suite (an isolated fake `TDA` module via `LEAN_PATH`) can't
# reliably reproduce Lean's auto-generated-name convention from scratch, and the exact
# declarations this regression is about already exist in the real sources. Run this
# after `scripts/check.sh`, not standalone on a cold build.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
if [ "$#" -ne 0 ]; then
  echo 'usage: scripts/test-audit-auxlemma.sh' >&2
  exit 64
fi

NAMES=(
  "TDA.Persistence.ofIndexBars._proof_1"
  "TDA.Persistence.dgm._proof_1"
  "TDA.Persistence.FiniteInterval.restrictAlong._proof_1"
)

# If a future refactor removes or renames these pins, this test must not pass vacuously
# (it would then be testing nothing): fail loudly and ask for a replacement declaration.
for name in "${NAMES[@]}"; do
  if ! grep -qF "#print axioms $name" scripts/print_axioms/Persistence.lean; then
    echo "FAIL: '$name' is no longer pinned in scripts/print_axioms/Persistence.lean." >&2
    echo "  This regression needs some pinned declaration whose name Lean's auxLemma" >&2
    echo "  linter recognises as auto-generated (a '._proof_N' suffix); update the" >&2
    echo "  NAMES list above to a current one, do not delete this test." >&2
    exit 1
  fi
done

out="$(bash scripts/check-axioms.sh 2>&1)" || {
  printf '%s\n' "$out" >&2
  echo "FAIL: scripts/check-axioms.sh did not pass (run scripts/check.sh first if the build is stale)." >&2
  exit 1
}

fail=0
for name in "${NAMES[@]}"; do
  if ! grep -qF "OK: $name " <<<"$out"; then
    echo "FAIL: '$name' was not reported OK — silently skipped, or its record was corrupted again?" >&2
    fail=1
  fi
done
if grep -qE 'warning:.*auxLemma|refers to an auto-generated auxiliary declaration' <<<"$out"; then
  echo "FAIL: the auxLemma linter fired; 'set_option linter.auxLemma false' in the generated file is not taking effect." >&2
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "auxLemma suppression regression OK — ${#NAMES[@]} auto-generated-name pin(s) genuinely audited"
else
  exit 1
fi
