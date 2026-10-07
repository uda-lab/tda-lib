#!/usr/bin/env bash
# argv-safe raw Lean/Lake entry point. No eval and no session-wide lock.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$PATH:$HOME/.elan/bin"
case "${1:-}" in lake|lean) tool=$1; shift ;; *) echo 'usage: scripts/lean.sh {lake|lean} <arguments...>' >&2; exit 64 ;; esac
for arg in "$@"; do
  case "$arg" in -M*|-j*|--memory=*|--memory|--threads=*|--threads) echo 'ERROR: manual -M/-j/memory/thread CLI limits are forbidden; use LEAN_NUM_THREADS.' >&2; exit 64 ;; esac
done
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
[[ "$LEAN_NUM_THREADS" =~ ^[1-9][0-9]*$ ]] || { echo 'ERROR: LEAN_NUM_THREADS must be positive' >&2; exit 64; }
if [ -e "${CODEX_STOP_FILE:-/tmp/codex-stop}" ]; then echo "ERROR: stopped by ${CODEX_STOP_FILE:-/tmp/codex-stop}" >&2; exit 2; fi
. "$ROOT/scripts/lib/build-lock.sh"
if [ -e "${CODEX_STOP_FILE:-/tmp/codex-stop}" ]; then echo "ERROR: stopped by ${CODEX_STOP_FILE:-/tmp/codex-stop}" >&2; exit 2; fi
. "$ROOT/scripts/lib/resources.sh"
lean_check_headroom
exec "$tool" "$@"
