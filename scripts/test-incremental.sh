#!/usr/bin/env bash
# Self-tests for the incremental local gate (scripts/check.sh --incremental, Issue #951).
#
# Requires a warm build already in this checkout (scripts/bootstrap.sh, then a `lake build`
# — e.g. a prior `scripts/check.sh` run); this file never triggers a cold build itself.
# Most cases use scripts/check-incremental.sh's TDA_INCREMENTAL_DRY_RUN test hook (documented
# in that file) to exercise the fallback/corruption DECISION without paying for the
# expensive audit/coverage/comparator steps on every case. Three cases are real end-to-end
# runs and are correspondingly the slow part of this file: populating a fresh record store
# (a genuine full-mode run, so that code path itself — not just the decision to take it — is
# exercised at least once), a genuine selective leaf-module audit, and the two real-bug
# cases (sorry, unpinned theorem) that must be caught by the selective audit's own
# `collectAxioms`/coverage logic, not merely by the unrelated textual guards.
#
# Uses a private, throwaway TDA_AUDIT_RECORDS directory; never touches the real one.
# Edits this checkout's real TDA/, scripts/print_axioms/ and scripts/lib/ files temporarily
# and restores every one of them from its own byte-for-byte backup (not `git checkout --`,
# which cannot restore a file this branch has not yet committed — several of #951's own
# files are still untracked while this PR is in flight) before exiting, success or failure
# alike.
#
# Serialises on the same build lock as scripts/check.sh; do not run concurrently with
# another build in this container.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

CACHE_PY="$ROOT/scripts/lib/incremental-cache.py"
fail=0

pass() { echo "PASS [$1]"; }
failcase() { echo "FAIL [$1]: $2" >&2; fail=1; }
# diagnostic <out>: both ends of a long capture, not just the tail — a `tail`-only capture
# once hid the actual "ERROR: axiom coverage failed." header line (and the real cause) behind
# thousands of lines of `lake build` progress, leaving only an unexplained MISSING list.
diagnostic() {
  local out="$1" n
  n="$(printf '%s' "$out" | wc -l | tr -d ' ')"
  if [ "$n" -le 40 ]; then
    printf '%s' "$out"
  else
    printf 'Head:\n%s\n…\nTail:\n%s' "$(printf '%s' "$out" | head -20)" "$(printf '%s' "$out" | tail -20)"
  fi
}

# A path that does not exist YET (not merely an empty directory `mktemp -d` already created):
# scripts/check-incremental.sh's own "record store does not exist yet" trigger
# (fallback-reason text "the incremental-audit record store does not exist yet") tests
# `[ ! -d "$store_path" ]`, which an already-existing empty directory never satisfies — the
# `fresh_store_forces_full` case below was passing for an entirely different, unintended
# reason (a sensitive-path diff) until this was fixed.
STORE_PARENT="$(mktemp -d)"
STORE="$STORE_PARENT/store"
export TDA_AUDIT_RECORDS="$STORE"
# #951's own branch permanently differs from origin/develop in every "sensitive" path this
# gate watches (lakefile.toml excepted; it's the gate's own scripts, lib and check.sh that
# differ) — that is the entire content of this PR. Diffing against real origin/develop would
# therefore make every git-diff-based trigger below fire for THAT reason first, on every
# case, masking whichever specific trigger each case means to isolate. A local branch ref
# pinned at this run's own HEAD gives check-incremental.sh's test-only
# TDA_INCREMENTAL_INTEGRATION_REF override (see its own comment) a merge-base with zero
# ambient diff, so only each case's own probe mutation shows up. TDA_INCREMENTAL_SELF_TEST=1
# is required too, so exporting TDA_INCREMENTAL_INTEGRATION_REF for some unrelated reason can
# never silently redirect a real invocation's comparison base.
BASELINE_REF="test-incremental-951-baseline-$$"
git branch -f "$BASELINE_REF" HEAD >/dev/null || { echo "FAIL [setup]: could not create the baseline ref $BASELINE_REF" >&2; exit 1; }
export TDA_INCREMENTAL_SELF_TEST=1
export TDA_INCREMENTAL_INTEGRATION_REF="$BASELINE_REF"
BACKUP_DIR="$(mktemp -d)"
declare -A BACKUP_OF
CREATED=()
# backup_then_touch <path>: snapshot <path>'s current bytes before the caller mutates it, by
# copy rather than `git checkout --`, so this works identically whether <path> is tracked,
# staged-new or (as with several of #951's own files, mid-PR) wholly untracked.
backup_then_touch() {
  # `${#BACKUP_OF[@]}` (an empty associative array's element COUNT, as opposed to iterating
  # it) is unbound under `set -u` in bash 5.2 even after `declare -A`; `mktemp` sidesteps it.
  local f="$1" b
  b="$(mktemp "$BACKUP_DIR/backup-XXXXXX-$(basename "$f")")"
  cp "$f" "$b"
  BACKUP_OF["$f"]="$b"
}
# restore_touched <path>: put back the exact bytes backup_then_touch saved.
restore_touched() {
  local f="$1"
  if [ -n "${BACKUP_OF[$f]:-}" ]; then
    cp "${BACKUP_OF[$f]}" "$f"
  fi
}
cleanup() {
  rm -rf "$STORE_PARENT"
  local f
  for f in "${!BACKUP_OF[@]}"; do
    cp "${BACKUP_OF[$f]}" "$f" 2>/dev/null || true
  done
  rm -rf "$BACKUP_DIR"
  if [ "${#CREATED[@]}" -gt 0 ]; then
    rm -f "${CREATED[@]}"
  fi
  git branch -D "$BASELINE_REF" >/dev/null 2>&1 || true
}
trap cleanup EXIT

run_incremental() { bash scripts/check.sh --incremental; }
dry_run() { TDA_INCREMENTAL_DRY_RUN="$1" bash scripts/check-incremental.sh; }
# dry_run_leaked <n>: the same direct invocation as dry_run, but WITHOUT
# TDA_INCREMENTAL_SELF_TEST — simulates TDA_INCREMENTAL_DRY_RUN leaking into a real
# invocation's environment on its own (some unrelated shell state, a misconfigured CI step),
# which must be ignored.
dry_run_leaked() { env -u TDA_INCREMENTAL_SELF_TEST TDA_INCREMENTAL_DRY_RUN="$1" bash scripts/check-incremental.sh; }

# =====================================================================================
# Cheap cases: no build, no lock needed.
# =====================================================================================

if out="$(bash scripts/check.sh --incremental --stable 2>&1)"; then
  failcase mutually_exclusive_flags "expected a nonzero exit; got 0. Output: $out"
else
  status=$?
  [ "$status" -eq 64 ] && pass mutually_exclusive_flags \
    || failcase mutually_exclusive_flags "expected exit 64, got $status"
fi

if [ -f .github/workflows/ci.yml ] && grep -E 'check\.sh' .github/workflows/ci.yml | grep -q -- '--incremental'; then
  failcase ci_workflow_plain "ci.yml must invoke scripts/check.sh without --incremental"
else
  pass ci_workflow_plain
fi

# Plain scripts/check.sh is structurally incapable of touching the record store: none of
# the full gate's own step scripts reference it, and scripts/check.sh's own only mention of
# it is inside its `$incremental = 1` branch.
store_leak=0
for f in scripts/check-axioms.sh scripts/check-axiom-coverage.sh scripts/check_axiom_coverage.lean; do
  grep -q 'incremental-cache\|TDA_AUDIT_RECORDS' "$f" && store_leak=1
done
mention_lines="$(grep -n 'check-incremental\.sh\|TDA_AUDIT_RECORDS' scripts/check.sh | cut -d: -f1)"
guard_start="$(grep -n '"\$incremental" = 1 \]; then' scripts/check.sh | cut -d: -f1 | head -1)"
guard_end="$(awk -v s="${guard_start:-0}" 'NR > s && /^fi$/ { print NR; exit }' scripts/check.sh)"
for ln in $mention_lines; do
  if [ -z "$guard_start" ] || [ "$ln" -lt "$guard_start" ] || [ "$ln" -gt "${guard_end:-0}" ]; then
    store_leak=1
  fi
done
if [ "$store_leak" -eq 1 ]; then
  failcase plain_never_reads_store "a reference to the incremental record store exists outside scripts/check.sh's --incremental branch"
else
  pass plain_never_reads_store
fi

# A pure, uncommitted ADDITION to scripts/print_axioms/ (no deleted/modified line) still
# forces the full gate here — deliberately broader than the Issue's literal wording; see
# scripts/check-incremental.sh's own comment for why.
pin_file="scripts/print_axioms/Basic.lean"
backup_then_touch "$pin_file"
printf '\n-- test-incremental.sh: self-test probe comment, reverted immediately\n' >>"$pin_file"
out="$(dry_run 1)"; status=$?
restore_touched "$pin_file"
if [ "$status" -eq 0 ] && printf '%s' "$out" | grep -q 'print_axioms/ changed'; then
  pass print_axioms_addition_forces_full
else
  failcase print_axioms_addition_forces_full "expected fallback reason mentioning print_axioms/; got: $out"
fi

# A build/toolchain/guard input changing (this incremental gate's own helper) forces the
# full gate: "a changed audit-tool source forces the full gate."
tool_file="scripts/lib/incremental-cache.py"
backup_then_touch "$tool_file"
printf '\n# test-incremental.sh: self-test probe comment, reverted immediately\n' >>"$tool_file"
out="$(dry_run 1)"; status=$?
restore_touched "$tool_file"
if [ "$status" -eq 0 ] && printf '%s' "$out" | grep -q "build/toolchain/guard input changed: $tool_file"; then
  pass changed_audit_tool_source_forces_full
else
  failcase changed_audit_tool_source_forces_full "expected fallback reason mentioning a changed guard input; got: $out"
fi

# A TDA/**/*.lean file that exists on disk but is reachable from nothing (not imported,
# directly or transitively, by TDA.lean) is caught by `incremental-cache.py keys`'s static
# reachability check (Issue #951 step 6, "Unloaded files") — purely from source text, before
# any build: Lake's default lean_lib glob would otherwise happily build this file too, so the
# declared/built comparison alone cannot see the bug.
orphan_file="TDA/_SelfTestOrphanProbe951.lean"
CREATED+=("$orphan_file")
printf -- '-- test-incremental.sh: self-test orphan-module probe, deleted immediately\ntheorem _selfTestOrphanProbe951Thm : True := trivial\n' >"$orphan_file"
out="$(python3 "$CACHE_PY" keys 2>&1)"; status=$?
rm -f "$orphan_file"
if [ "$status" -ne 0 ] && printf '%s' "$out" | grep -q 'not reachable from TDA.lean'; then
  pass orphan_module_not_reachable
else
  failcase orphan_module_not_reachable "expected a nonzero exit citing unreachable-from-TDA.lean; status=$status. Output: $out"
fi

# A modified (not just deleted) existing pin line also forces the full gate.
backup_then_touch "$pin_file"
sed -i '1s/^/-- test-incremental.sh: self-test probe, reverted immediately\n/' "$pin_file"
out="$(dry_run 1)"; status=$?
restore_touched "$pin_file"
if [ "$status" -eq 0 ] && printf '%s' "$out" | grep -q 'print_axioms/ changed'; then
  pass modified_pin_line_forces_full
else
  failcase modified_pin_line_forces_full "expected fallback reason mentioning print_axioms/; got: $out"
fi

# Pre-push gate selection and source binding run in real temporary Git repositories.
# Their scripts/check.sh stubs are tracked inside each fixture, so this checkout stays clean.
if bash scripts/test-pre-push.sh; then
  pass pre_push_source_binding_and_gate_selection
else
  failcase pre_push_source_binding_and_gate_selection "isolated pre-push fixture suite failed"
fi

# =====================================================================================
# Real end-to-end cases: these actually run (or decide after running) `lake build` and, at
# least once, the real audit. Slow; this is why this file is not part of the fast guard
# suite loop.
# =====================================================================================

# This run is also the natural place to prove a leaked TDA_COMPARATOR_SKIP_SANDBOXED_RUN is
# ignored: the store is empty, so the Comparator step below MUST genuinely run (a miss/
# full-mode case) if the leak is correctly neutralised — exactly the scenario where honouring
# an ambient leak would otherwise skip the real sandboxed run and still write a Comparator
# PASS record other worktrees would reuse. Reuses this call rather than paying for a second
# full gate run just to exercise the leak.
echo "==> test-incremental.sh: populating a fresh record store (real full-mode run)"
out="$(TDA_COMPARATOR_SKIP_SANDBOXED_RUN=1 run_incremental 2>&1)"; status=$?
if [ "$status" -eq 0 ] && printf '%s' "$out" | grep -q 'INCREMENTAL CHECK OK (fell back to full: the incremental-audit record store does not exist yet'; then
  pass fresh_store_forces_full
else
  failcase fresh_store_forces_full "expected a successful full-mode fallback citing the missing store; status=$status.
$(diagnostic "$out")"
fi
if ! printf '%s' "$out" | grep -q 'Comparator sandboxed run skipped'; then
  pass leaked_comparator_skip_ignored
else
  failcase leaked_comparator_skip_ignored "a leaked TDA_COMPARATOR_SKIP_SANDBOXED_RUN=1 must never skip the sandboxed run on a miss/full-mode path; got:
$(diagnostic "$out")"
fi
record_count="$(find "$STORE" -maxdepth 1 -name '*.json' | wc -l | tr -d ' ')"
if [ "$record_count" -gt 900 ]; then
  pass full_mode_refreshed_records
else
  failcase full_mode_refreshed_records "expected >900 refreshed records after the full-mode run, found $record_count"
fi

# A leaked TDA_INCREMENTAL_DRY_RUN (set in some unrelated shell state or a misconfigured CI
# step, without the self-test marker) must never make a real invocation print "DRY RUN ..."
# and exit 0 without auditing anything. Dropping TDA_INCREMENTAL_SELF_TEST also disables the
# TDA_INCREMENTAL_INTEGRATION_REF override for this one call (by the same marker, on purpose
# — a real leak would not selectively disable one test-only override but not the other), so
# this call compares against real origin/develop and correctly falls back to full mode for
# the unrelated reason that #951's own branch differs from it in sensitive paths; either way,
# the only thing this case needs to prove is the absence of a "DRY RUN" short-circuit.
out="$(dry_run_leaked 1 2>&1)"; status=$?
if [ "$status" -eq 0 ] && ! printf '%s' "$out" | grep -q '^DRY RUN' \
    && printf '%s' "$out" | grep -qE 'INCREMENTAL CHECK OK'; then
  pass leaked_dry_run_ignored
else
  failcase leaked_dry_run_ignored "expected the real gate to run despite a leaked TDA_INCREMENTAL_DRY_RUN=1 (no self-test marker); status=$status.
$(diagnostic "$out")"
fi

# Pick a TDA content module to edit for the remaining cases, via `smallest-leaf`: this
# project's area/root aggregators import every real content module, so (per its own
# docstring and `graph`'s) NO non-root module ever has a direct reverse-dependency count of
# 0 — editing any one of them necessarily also changes every ancestor aggregator's own key,
# all the way up to the root. `smallest-leaf` instead picks the content module whose full
# reverse closure (itself plus every transitive importer — the Issue acceptance test's
# "that module and its reverse dependencies") is smallest, so the edits below stay fast and
# the audited-count assertion below can be exact rather than merely "more than zero".
leaf_line="$(python3 "$CACHE_PY" smallest-leaf)"
leaf="${leaf_line%%$'\t'*}"
expected_audited="${leaf_line##*$'\t'}"
if [ -z "$leaf" ] || [ -z "$expected_audited" ]; then
  failcase pick_leaf_module "no suitable TDA content module was found; cannot run the remaining real cases"
else
  leaf_path="$(printf '%s' "$leaf" | sed 's/\./\//g').lean"
  if [ ! -f "$leaf_path" ]; then
    failcase pick_leaf_module "computed path $leaf_path for leaf module $leaf does not exist"
  else
    echo "==> test-incremental.sh: using $leaf ($leaf_path), reverse-closure size $expected_audited, as the test leaf"

    # --- corrupted record forces the full gate (checked via dry run; restored after) -----
    corrupt_key_line="$(python3 "$CACHE_PY" keys | awk -F'\t' -v m="$leaf" '$1 == m')"
    corrupt_key="${corrupt_key_line#*$'\t'}"
    corrupt_record="$STORE/$corrupt_key.json"
    cp "$corrupt_record" "$corrupt_record.bak"
    printf 'not valid json{{{' >"$corrupt_record"
    out="$(dry_run 2)"; status=$?
    mv "$corrupt_record.bak" "$corrupt_record"
    if [ "$status" -eq 0 ] && printf '%s' "$out" | grep -q 'corrupt or invalid incremental-audit record'; then
      pass corrupted_record_forces_full
    else
      failcase corrupted_record_forces_full "expected fallback reason mentioning a corrupt record; got: $out"
    fi

    # --- leaf edit re-audits exactly its reverse closure (Issue acceptance: "that module
    # and its reverse dependencies") -------------------------------------------------------
    # A real declaration, not just a comment: Lean's olean serialisation may not change a
    # single byte for a comment appended after every existing declaration (no source
    # position shifts), which would make this case pass for the wrong reason (nothing to
    # re-audit) rather than the right one. Editing $leaf changes its own key AND, because
    # its forward closure is now part of every reverse-dependent aggregator's forward
    # closure too, each of their keys — exactly $expected_audited modules, no more (nothing
    # outside the reverse closure) and no fewer (every module above the edit is stale).
    backup_then_touch "$leaf_path"
    printf '\nprivate theorem _selfTestLeafEditProbe951 : True := trivial -- #951 self-test probe, reverted immediately\n' >>"$leaf_path"
    out="$(run_incremental 2>&1)"; status=$?
    restore_touched "$leaf_path"
    if [ "$status" -eq 0 ] && printf '%s' "$out" | grep -qE "INCREMENTAL CHECK OK — audited ${expected_audited}/[0-9]+ modules"; then
      pass leaf_edit_audits_exact_reverse_closure
    else
      failcase leaf_edit_audits_exact_reverse_closure "expected a selective run auditing exactly $expected_audited module(s); status=$status.
$(diagnostic "$out")"
    fi

    # --- a sorry (behind ALLOW_SORRY, so the textual guard itself still passes) is caught
    # by the selective audit's own collectAxioms check, not only by the full gate's -------
    backup_then_touch "$leaf_path"
    printf '\nprivate theorem _selfTestSorryProbe951 : True := sorry -- ALLOW_SORRY: #951 self-test probe, reverted immediately\n' >>"$leaf_path"
    out="$(run_incremental 2>&1)"; status=$?
    restore_touched "$leaf_path"
    if [ "$status" -ne 0 ] && printf '%s' "$out" | grep -q 'sorryAx'; then
      pass sorry_caught_by_selective_audit
    else
      failcase sorry_caught_by_selective_audit "expected a nonzero exit citing sorryAx; status=$status.
$(diagnostic "$out")"
    fi

    # --- a new, unpinned public theorem fails coverage ------------------------------------
    # No leading underscore: Lean's own `Name.isInternal` (`s.front == '_'`) makes
    # `isAutoDeclOrPrivate_Internal` treat ANY underscore-prefixed name as auto-generated,
    # which `isPublicProjectTheorem`/`isPublicScopedTheorem` exclude from "public theorem"
    # classification entirely — by design, correctly, for every OTHER such name in this
    # project. An underscore-prefixed probe here would be invisible to the coverage check
    # it means to test, not merely unpinned; it was never audited for axioms either.
    backup_then_touch "$leaf_path"
    printf '\ntheorem selfTestUnpinnedProbe951 : True := trivial\n' >>"$leaf_path"
    out="$(run_incremental 2>&1)"; status=$?
    restore_touched "$leaf_path"
    if [ "$status" -ne 0 ] && printf '%s' "$out" | grep -q 'not pinned'; then
      pass new_unpinned_theorem_fails
    else
      failcase new_unpinned_theorem_fails "expected a nonzero exit citing an unpinned theorem; status=$status.
$(diagnostic "$out")"
    fi
  fi
fi

if [ "$fail" -eq 0 ]; then
  echo "INCREMENTAL GATE SELF-TESTS OK"
else
  echo "INCREMENTAL GATE SELF-TESTS FAILED" >&2
  exit 1
fi
