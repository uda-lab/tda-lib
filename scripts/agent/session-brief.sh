#!/usr/bin/env bash
# Read-only session context; the guarded no-build status check may wait on resource locks.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
. "$ROOT/scripts/lib/resources.sh"
avail=$(lean_available_kib)
if [ -n "$avail" ]; then memory="$((avail / 1024)) MiB"; else memory=unknown; fi
lean_resolve_num_threads 2>/dev/null
cache_dir=$(python3 "$ROOT/scripts/lib/build-resources.py" --artifact-cache-dir "$ROOT" 2>/dev/null) || cache_dir=unknown
if [ -n "$cache_dir" ]; then
  cache_status="$cache_dir"
else
  cache_status='disabled by LAKE_CACHE_DIR'
fi
if (cd "$ROOT" && "$ROOT/scripts/lean.sh" lake build --no-build TDA >/dev/null 2>&1); then
  warm_status='current (exit 0)'
else
  probe_status=$?
  warm_status="stale or unavailable (probe exit $probe_status)"
fi
printf '%s\n' "$(basename "$ROOT") session brief:" \
  "- memory headroom: $memory; required ${LEAN_GUARD_MIN_AVAIL_MIB:-1536} MiB" \
  "- Lean threads per process: ${LEAN_NUM_THREADS:-unknown} (${LEAN_NUM_THREADS_SOURCE:-unknown}; ${LEAN_NUM_THREADS_DETECTED:-unknown} detected); concurrent builds need separate resource coordination." \
  "- Lake artifact cache: $cache_status; new worktree: scripts/bootstrap.sh then scripts/check.sh; warm build probe: $warm_status (scripts/lean.sh lake build --no-build TDA)." \
  '- Build exclusion: canonical shared checkout/build/dependency paths, including symlink targets.' \
  '- Lean/Lake: use scripts/lean.sh; check.sh and bootstrap.sh use the same runtime guard.' \
  '- Codex children: use scripts/codex.sh with LOOP_JOB_ID=<library>/<job>/<role>.' \
  '- Native hook command-text guard applies when the harness supports and enables trusted project hooks. Wrappers enforce resources independently.' \
  '- Canonical skills: .agents/skills; workflow: docs/orchestration.md.'
