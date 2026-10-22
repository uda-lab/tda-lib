#!/usr/bin/env bash
# argv-safe Lean/Lake entry point with shared-path exclusion and resource checks.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
export PATH="$PATH:$HOME/.elan/bin"
case "${1:-}" in lake|lean) tool=$1; shift ;; *) echo 'usage: scripts/lean.sh {lake|lean} <arguments...>' >&2; exit 64 ;; esac
# Lake resolves its project from cwd. Do not guard this checkout while building another.
if [ "$tool" = lake ]; then
  project="$(pwd -P)"
  while [ ! -f "$project/lakefile.toml" ] && [ ! -f "$project/lakefile.lean" ]; do
    [ "$project" != / ] || { echo 'ERROR: no Lake project in cwd ancestry' >&2; exit 64; }
    project=${project%/*}; project=${project:-/}
  done
  case "$project" in "$ROOT"|"$ROOT/docbuild") ;;
    *) echo 'ERROR: run the Lean wrapper from its own checkout or docbuild project.' >&2; exit 64 ;;
  esac
fi
for arg in "$@"; do
  if [ "$tool" = lake ]; then
    case "$arg" in -d|--dir|--dir=*|-d?*|-f|--file|--file=*|-f?*|-K*)
      echo 'ERROR: Lake project/config redirection is outside this wrapper resource set.' >&2; exit 64 ;;
    esac
  fi
  case "$arg" in -M*|-j*|--memory=*|--memory|--threads=*|--threads) echo 'ERROR: manual -M/-j/memory/thread CLI limits are forbidden; use LEAN_NUM_THREADS.' >&2; exit 64 ;; esac
done
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
[[ "$LEAN_NUM_THREADS" =~ ^[1-9][0-9]*$ ]] || { echo 'ERROR: LEAN_NUM_THREADS must be positive' >&2; exit 64; }
if [ -e "${CODEX_STOP_FILE:-/tmp/codex-stop}" ]; then echo "ERROR: stopped by ${CODEX_STOP_FILE:-/tmp/codex-stop}" >&2; exit 2; fi
python3 "$ROOT/scripts/lib/build-resources.py" --check-outputs "$ROOT" "$tool" "$@"
. "$ROOT/scripts/lib/build-lock.sh"
if [ -e "${CODEX_STOP_FILE:-/tmp/codex-stop}" ]; then echo "ERROR: stopped by ${CODEX_STOP_FILE:-/tmp/codex-stop}" >&2; exit 2; fi
. "$ROOT/scripts/lib/resources.sh"
lean_check_headroom
exec "$tool" "$@"
