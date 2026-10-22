#!/usr/bin/env bash
# Read-only session context; never waits on build locks or kills processes.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
. "$ROOT/scripts/lib/resources.sh"
avail=$(lean_available_kib)
if [ -n "$avail" ]; then memory="$((avail / 1024)) MiB"; else memory=unknown; fi
printf '%s\n' "$(basename "$ROOT") session brief:" \
  "- memory headroom: $memory; required ${LEAN_GUARD_MIN_AVAIL_MIB:-1536} MiB" \
  "- Lean threads per process: ${LEAN_NUM_THREADS:-1 (conservative fallback)}; concurrent builds need separate resource coordination." \
  '- Build exclusion: canonical shared checkout/build/dependency paths, including symlink targets.' \
  '- Lean/Lake: use scripts/lean.sh; check.sh and bootstrap.sh use the same runtime guard.' \
  '- Codex children: use scripts/codex.sh with LOOP_JOB_ID=<library>/<job>/<role>.' \
  '- Native hook command-text guard applies when the harness supports and enables trusted project hooks. Wrappers enforce resources independently.' \
  '- Canonical skills: .agents/skills; workflow: docs/orchestration.md.'
