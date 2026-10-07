#!/usr/bin/env bash
# Claude compatibility adapter; canonical implementation is harness-neutral.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
exec bash "$ROOT/scripts/agent/test-codex-chains.sh" "$@"
