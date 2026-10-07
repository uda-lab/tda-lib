#!/usr/bin/env bash
# Self-test for the ownership-aware codex-chain cleanup in codex-chains.sh. Spawns fake chain
# processes (a script named `codex` run as `codex app-server`, so comm and argv match the real
# ones) under a unique job-id prefix; real chains on the machine never match it.
# Run after every edit of the helper:  bash scripts/agent/test-codex-chains.sh
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ ! -d /proc/self ]; then echo "codex-chain self-test SKIPPED (no /proc)"; exit 0; fi
unset LOOP_JOB_ID
# shellcheck source=codex-chains.sh
. "$HERE/codex-chains.sh"

tmp="$(mktemp -d)"; pids=()
cleanup() { for p in "${pids[@]}"; do kill "$p" 2>/dev/null; done; rm -rf "$tmp"; }
trap cleanup EXIT
mkdir -p "$tmp/bin"
cat > "$tmp/bin/codex" <<'EOF'
#!/bin/sh
trap 'kill $! 2>/dev/null; exit 0' TERM
env -u LOOP_JOB_ID sleep 300 &
wait
EOF
chmod +x "$tmp/bin/codex"
L="TestLib$$"
fail=0; n=0

spawn_chain() {  # spawn_chain <job-id|-> <cwd> [delete-cwd]  → sets $last
  local job="$1" dir="$2"
  mkdir -p "$dir"
  if [ "$job" = - ]; then
    (cd "$dir" && exec env -u LOOP_JOB_ID "$tmp/bin/codex" app-server) &
  else
    (cd "$dir" && exec env LOOP_JOB_ID="$job" "$tmp/bin/codex" app-server) &
  fi
  last=$!; pids+=("$last")
  [ "${3:-}" = delete ] && { sleep 0.2; rmdir "$dir"; }
}
expect() {  # expect <name> <want: yes|no> <pid> <reapable args...>
  local name="$1" want="$2" pid="$3" got=no list; shift 3
  n=$((n + 1))
  list=" $(codex_chains_reapable "$@" | tr '\n' ' ') "   # captured: grep -q in a pipe trips pipefail
  case "$list" in *" $pid "*) got=yes ;; esac
  [ "$got" = "$want" ] || { echo "FAIL [$name]: want $want got $got"; fail=1; }
}

spawn_chain "$L/issue-1/driver" "$tmp/w1"; c1=$last
spawn_chain "$L/issue-2/driver" "$tmp/w2"; c2=$last
(exec env LOOP_JOB_ID="$L/issue-2/driver" sleep 300) & pids+=("$!")     # issue-2 still working
spawn_chain - "$tmp/w3" delete; c3=$last                                 # untagged, removed worktree
spawn_chain "$L/issue-4/driver" "$tmp/w4"; c4=$last                      # finished, worktree kept
spawn_chain "$L/issue-5/driver" "$tmp/w5" delete; c5=$last               # finished, worktree removed
spawn_chain "Other$$/issue-5/driver" "$tmp/w6" delete; c6=$last          # another repository's job
sleep 0.5

expect owned_finished_job           yes "$c1" "$L/issue-1/driver"
expect owned_job_still_working      no  "$c2" "$L/issue-2/driver"
expect other_job_not_mine           no  "$c1" "$L/issue-2/driver"
expect untagged_deleted_cwd_sweep   no  "$c3" "$L/*" --deleted-cwd-only
expect untagged_any_pattern         no  "$c3" '*'
expect sweep_needs_deleted_cwd      no  "$c4" "$L/*" --deleted-cwd-only
expect sweep_finished_deleted_cwd   yes "$c5" "$L/*" --deleted-cwd-only
expect sweep_other_repository       no  "$c6" "$L/*" --deleted-cwd-only
expect sweep_skips_live_job         no  "$c2" "$L/*"

n=$((n + 1))
if (LOOP_JOB_ID=x; export LOOP_JOB_ID; codex_chains_reapable '*' >/dev/null 2>&1); then
  echo "FAIL [refuse_tagged_caller]: ran with LOOP_JOB_ID set"; fail=1
fi

n=$((n + 1))
got="$(reap_codex_chains "$L/issue-1/driver")"; sleep 0.3
if [ "$got" != 1 ] || kill -0 "$c1" 2>/dev/null || ! kill -0 "$c2" 2>/dev/null; then
  echo "FAIL [reap_signals_only_owned]: count $got, c1 alive=$(kill -0 "$c1" 2>/dev/null && echo y), c2 alive=$(kill -0 "$c2" 2>/dev/null && echo y)"; fail=1
fi

if [ "$fail" -eq 0 ]; then echo "codex-chain self-test OK ($n cases)"; else exit 1; fi
