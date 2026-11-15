#!/usr/bin/env bash
# The local pre-PR gate for Issue #951, invoked ONLY by `scripts/check.sh --incremental`
# (never directly): that caller already ran the textual guards, holds the build lock, and
# has `cd`'d to the repository root with `GIT_DIR`/`GIT_WORK_TREE`/`GIT_INDEX_FILE` cleared.
# It re-runs `lake build` and then re-audits axioms/coverage/Comparator only for whatever a
# content-hashed key shows has no recorded local pass; whenever eligibility itself cannot be
# established, it runs the full gate instead and refreshes the records from that run. It is
# feedback, not merge evidence: its final line never reads `CHECK OK`. See
# scripts/lib/incremental-cache.py's module docstring for the cache key's soundness argument.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

CACHE_PY="$ROOT/scripts/lib/incremental-cache.py"
SCRATCH="$ROOT/.agents/scratch"
mkdir -p "$SCRATCH"
WORK="$(mktemp -d "$SCRATCH/incremental.XXXXXX")"
trap 'rm -rf "$WORK" "$SCRATCH/incremental-audit-scope.txt" "$SCRATCH/incremental-audit-output.json"' EXIT

step() { echo "==> $*"; }

solution_module="TDA.Probability.SamplingCoverage"

# --- Step 2 (part 1): static fallback triggers, decided before anything is read -----------
fallback_reason=""

integration=origin/develop
if ! git rev-parse --verify "$integration" >/dev/null 2>&1; then integration=origin/main; fi
merge_base="$(git merge-base HEAD "$integration" 2>/dev/null)"
if [ -z "$merge_base" ]; then
  fallback_reason="the merge base with $integration could not be computed"
fi

changed_files=""
if [ -z "$fallback_reason" ]; then
  # Includes uncommitted changes, matching the pre-push hook building the working tree.
  if ! changed_files="$(git diff --name-only "$merge_base" -- . 2>&1)"; then
    fallback_reason="the diff from the merge base to the working tree could not be computed"
    changed_files=""
  fi
fi

# Any change to scripts/print_axioms/*.lean — added, modified or deleted lines alike. This is
# deliberately broader than the Issue's literal "deleted or modified": a pure addition could
# pin a declaration whose own module did not change, and this gate cannot safely resolve a
# name by itself without importing an a-priori-unknown module (see the PR for the full
# reasoning). The coarser trigger stays sound; it only gives up some incremental benefit on
# PRs that also add pins.
if [ -z "$fallback_reason" ] && printf '%s\n' "$changed_files" | grep -qE '^scripts/print_axioms/'; then
  fallback_reason="scripts/print_axioms/ changed relative to the merge base"
fi

# Any build/toolchain/guard input this gate's own soundness, or the full gate's behaviour,
# depends on: lakefile.toml, lake-manifest.json, lean-toolchain, the full gate's own
# audit/coverage/comparator scripts, this incremental gate's own scripts (so a change to the
# mechanism itself is never trusted against records it predates), scripts/lean.sh and the
# shared lexer.
sensitive_regex='^(lakefile\.toml|lake-manifest\.json|lean-toolchain|scripts/check-axioms\.sh|scripts/check-axiom-coverage\.sh|scripts/check_axiom_coverage\.lean|scripts/check\.sh|scripts/check-incremental\.sh|scripts/check-comparator\.sh|scripts/lean\.sh|scripts/lean-code-scan\.awk|scripts/lib/.*)$'
if [ -z "$fallback_reason" ] && printf '%s\n' "$changed_files" | grep -qE "$sensitive_regex"; then
  hit="$(printf '%s\n' "$changed_files" | grep -E "$sensitive_regex" | head -1)"
  fallback_reason="a build/toolchain/guard input changed: $hit"
fi

# A record store that does not exist yet (fresh clone/worktree, or TDA_AUDIT_RECORDS pointed
# somewhere new) is its own explicit trigger, distinct from an ordinary per-module cache miss:
# run the proven full-gate code path rather than exercising the selective path's "nothing is
# cached yet" degenerate case, which provides no incremental benefit anyway.
store_path="$(python3 "$CACHE_PY" store-dir)"
if [ -z "$fallback_reason" ] && [ ! -d "$store_path" ]; then
  fallback_reason="the incremental-audit record store does not exist yet ($store_path)"
fi

# Test-only early exit (scripts/test-incremental.sh): report the purely git/file-diff-based
# part of Step 2 without needing a build at all. Never set by any real invocation.
if [ "${TDA_INCREMENTAL_DRY_RUN:-0}" = 1 ]; then
  echo "DRY RUN 1: fallback_reason=${fallback_reason:-(none)}"
  exit 0
fi

# --- Step 3: lake build (Lake's own incrementality; unconditional either way) --------------
step "lake build"
if ! "$ROOT/scripts/lean.sh" lake build; then
  echo "ERROR: lake build failed." >&2
  exit 1
fi

# --- Compute every module's current key (needed in both modes, to refresh records) --------
keys_output=""
keys_status=0
keys_output="$(python3 "$CACHE_PY" keys)" || keys_status=$?
if [ "$keys_status" -ne 0 ]; then
  [ -n "$fallback_reason" ] || fallback_reason="module key computation failed (see stderr above)"
  keys_output=""
fi
total_modules=0
[ -z "$keys_output" ] || total_modules="$(printf '%s\n' "$keys_output" | wc -l | tr -d ' ')"

# A module's key, from this run's `keys` output. Empty (and nonzero exit) if not found.
module_key() {
  printf '%s\n' "$keys_output" | awk -F'\t' -v m="$1" '$1 == m { print $2; found=1 } END { exit !found }'
}

pin_names() {
  find "$ROOT/scripts/print_axioms" -maxdepth 1 -type f -name '*.lean' -print0 \
    | xargs -0 awk '/^#print axioms /{print $3}' | sort -u
}

# --- Step 2 (part 2) / selective read: attempt every record only while still eligible ------
need_audit=()
reused_count=0
reused_declared_file="$WORK/reused.jsonl"
: >"$reused_declared_file"
comparator_key=""
comparator_cache_status=""  # "" (not attempted) | hit | miss
if [ -z "$fallback_reason" ]; then
  while IFS=$'\t' read -r module key; do
    [ -n "$module" ] || continue
    record_status=0
    record_json="$(python3 "$CACHE_PY" read-record "$key" audit)" || record_status=$?
    case "$record_status" in
      0) reused_count=$((reused_count + 1)); printf '%s\n' "$record_json" >>"$reused_declared_file" ;;
      2) need_audit+=("$module") ;;
      *) fallback_reason="corrupt or invalid incremental-audit record for module $module" ;;
    esac
    [ -z "$fallback_reason" ] || break
  done <<<"$keys_output"
fi
if [ -z "$fallback_reason" ]; then
  if solution_key="$(module_key "$solution_module")"; then
    comparator_key="$(python3 "$CACHE_PY" comparator-key "$solution_key")" || fallback_reason="Comparator key computation failed"
  else
    fallback_reason="no incremental-audit key for the Comparator solution module $solution_module"
  fi
fi
if [ -z "$fallback_reason" ]; then
  comparator_status=0
  python3 "$CACHE_PY" read-record "$comparator_key" comparator >/dev/null 2>"$WORK/comparator-read-err" || comparator_status=$?
  case "$comparator_status" in
    0) comparator_cache_status=hit ;;
    2) comparator_cache_status=miss ;;
    *) fallback_reason="corrupt or invalid Comparator record"; cat "$WORK/comparator-read-err" >&2 ;;
  esac
fi

# Test-only early exit (scripts/test-incremental.sh): report the full Step 2 decision,
# including key computation and record-corruption detection, after `lake build` (cheap once
# warm) but before the expensive audit/coverage/comparator steps either mode would run next.
# Never set by any real invocation.
if [ "${TDA_INCREMENTAL_DRY_RUN:-0}" = 2 ]; then
  echo "DRY RUN 2: fallback_reason=${fallback_reason:-(none)}; need_audit=${need_audit[*]-}; reused=$reused_count; comparator=$comparator_cache_status"
  exit 0
fi

# ------------------------------------------------------------------------------------------- #
# Full mode: run the unchanged full-gate steps unconditionally (no caching attempt for
# Comparator either, in this branch — simplest and always safe), then, only if keys were
# available, refresh every per-module record plus the Comparator record from this run's own
# already-passed output, with no second environment load
# (scripts/check_axiom_coverage.lean's additive side-car; see its header comment).
# ------------------------------------------------------------------------------------------- #
if [ -n "$fallback_reason" ]; then
  step "live axiom audit (full mode)"
  bash scripts/check-axioms.sh || { echo "ERROR: live axiom audit failed." >&2; exit 1; }
  step "axiom coverage (full mode)"
  bash scripts/check-axiom-coverage.sh || { echo "ERROR: axiom coverage failed." >&2; exit 1; }
  step "Comparator agreement (full mode)"
  bash scripts/check-comparator.sh || { echo "ERROR: Comparator agreement failed." >&2; exit 1; }

  if [ -n "$keys_output" ] && [ -s "$SCRATCH/full-gate-module-audit.json" ]; then
    step "refreshing incremental-audit records from this full-gate run"
    while IFS=$'\t' read -r module key; do
      [ -n "$module" ] || continue
      record="$(jq -c --arg m "$module" \
        '.modules[$m] // {"public":[],"declared":[]} | {schema: 1, kind: "audit", module: $m, public: .public, declared: .declared}' \
        "$SCRATCH/full-gate-module-audit.json")" \
        && printf '%s' "$record" | python3 "$CACHE_PY" write-record "$key" audit \
        || echo "WARNING: could not refresh the incremental-audit record for $module." >&2
    done <<<"$keys_output"
    if solution_key="$(module_key "$solution_module")" \
       && refreshed_comparator_key="$(python3 "$CACHE_PY" comparator-key "$solution_key")"; then
      printf '{"schema":1,"kind":"comparator"}' | python3 "$CACHE_PY" write-record "$refreshed_comparator_key" comparator \
        || echo "WARNING: could not refresh the Comparator record." >&2
    fi
  fi

  echo "INCREMENTAL CHECK OK (fell back to full: $fallback_reason)"
  exit 0
fi

# ------------------------------------------------------------------------------------------- #
# Selective mode: every module keeps or loses its cached pass independently; Comparator's
# sandboxed run is skipped independently of the audit/coverage decision, on its own key.
# ------------------------------------------------------------------------------------------- #
step "incremental audit: ${#need_audit[@]} module(s) need auditing, $reused_count reused"
fresh_json="$WORK/incremental-audit-output.json"
if [ "${#need_audit[@]}" -gt 0 ]; then
  : >"$SCRATCH/incremental-audit-scope.txt"
  generated="$WORK/incremental-audit-generated.lean"
  : >"$generated"
  for m in "${need_audit[@]}"; do
    printf 'import %s\n' "$m" >>"$generated"
    printf '%s\n' "$m" >>"$SCRATCH/incremental-audit-scope.txt"
  done
  cat "$ROOT/scripts/lib/incremental-audit-body.lean" >>"$generated"
  if ! "$ROOT/scripts/lean.sh" lake env lean "$generated"; then
    echo "ERROR: incremental audit failed for: ${need_audit[*]}" >&2
    exit 1
  fi
  mv -f "$SCRATCH/incremental-audit-output.json" "$fresh_json" 2>/dev/null \
    || { echo "ERROR: incremental audit produced no output." >&2; exit 1; }

  for m in "${need_audit[@]}"; do
    key="$(module_key "$m")" || { echo "ERROR: no key computed for audited module $m." >&2; exit 1; }
    record="$(jq -c --arg m "$m" \
      '.modules[$m] // {"public":[],"declared":[]} | {schema: 1, kind: "audit", module: $m, public: .public, declared: .declared}' \
      "$fresh_json")" || { echo "ERROR: could not read fresh audit output for $m." >&2; exit 1; }
    printf '%s' "$record" | python3 "$CACHE_PY" write-record "$key" audit \
      || { echo "ERROR: could not write incremental-audit record for $m." >&2; exit 1; }
  done
fi

# --- Pin cross-check: union declared/public names over reused + fresh records --------------
declared_all="$WORK/declared-union.txt"; public_all="$WORK/public-union.txt"
: >"$declared_all"; : >"$public_all"
if [ -s "$reused_declared_file" ]; then
  jq -r '.declared[]' "$reused_declared_file" >>"$declared_all"
  jq -r '.public[]' "$reused_declared_file" >>"$public_all"
fi
if [ -s "$fresh_json" ]; then
  jq -r '.modules[] | .declared[]' "$fresh_json" >>"$declared_all"
  jq -r '.modules[] | .public[]' "$fresh_json" >>"$public_all"
fi
sort -u -o "$declared_all" "$declared_all"
sort -u -o "$public_all" "$public_all"

pins_file="$WORK/pins.txt"
pin_names >"$pins_file"

missing_pins="$(comm -23 "$pins_file" "$declared_all")"
missing_coverage="$(comm -23 "$public_all" "$pins_file")"
pin_check_failed=0
if [ -n "$missing_pins" ]; then
  echo "ERROR: pinned declaration(s) not found among any module's audited/declared names (missing or renamed?):" >&2
  printf '%s\n' "$missing_pins" | sed 's/^/MISSING: /' >&2
  pin_check_failed=1
fi
if [ -n "$missing_coverage" ]; then
  echo "ERROR: public theorem(s) not pinned in scripts/print_axioms/:" >&2
  printf '%s\n' "$missing_coverage" | sed 's/^/MISSING: /' >&2
  pin_check_failed=1
fi
[ "$pin_check_failed" -eq 0 ] || exit 1

# --- Comparator: already decided hit/miss above; act on it now ----------------------------
step "Comparator agreement"
case "$comparator_cache_status" in
  hit)
    TDA_COMPARATOR_SKIP_SANDBOXED_RUN=1 bash scripts/check-comparator.sh \
      || { echo "ERROR: Comparator static checks failed even though the sandboxed run was skipped." >&2; exit 1; }
    ;;
  miss)
    bash scripts/check-comparator.sh || { echo "ERROR: Comparator agreement failed." >&2; exit 1; }
    printf '{"schema":1,"kind":"comparator"}' | python3 "$CACHE_PY" write-record "$comparator_key" comparator \
      || echo "WARNING: could not write the Comparator record." >&2
    ;;
  *)
    echo "ERROR: internal error — Comparator cache status was never decided." >&2
    exit 1
    ;;
esac

echo "INCREMENTAL CHECK OK — audited ${#need_audit[@]}/${total_modules} modules ($reused_count reused); full gate is hosted CI job \"check\""
