#!/usr/bin/env bash
# Guard child launch only: holding the Lean lock for a session would deadlock its builds.
set -euo pipefail
if [ -e "${CODEX_STOP_FILE:-/tmp/codex-stop}" ]; then echo "ERROR: Codex launch stopped by ${CODEX_STOP_FILE:-/tmp/codex-stop}; do not retry until cleared." >&2; exit 2; fi
if [[ ! "${LOOP_JOB_ID:-}" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]]; then
  echo 'ERROR: set LOOP_JOB_ID=<library>/<job>/<role> for owned child launch.' >&2; exit 64
fi
exec codex "$@"
