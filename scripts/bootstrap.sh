#!/usr/bin/env bash
# Per-clone setup. Idempotent and safe to re-run; performs no build.
#   - mathlib oleans via `lake exe cache get` (materialises the packages pinned in
#     lake-manifest.json on first run; never cold-builds mathlib, never runs `lake update`);
#   - git hooks path → scripts/hooks (pre-push gate).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found. Install elan (https://github.com/leanprover/elan);" >&2
  echo "       it installs the toolchain named in lean-toolchain on first use." >&2
  exit 1
fi

git config core.hooksPath scripts/hooks
echo "==> git hooks path: scripts/hooks"

echo "==> lake exe cache get"
lake exe cache get

echo "BOOTSTRAP OK — next: scripts/check.sh"
