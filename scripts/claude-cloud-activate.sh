#!/usr/bin/env bash
# Reuse only the exact pinned package sources prepared by claude-cloud-setup.sh.
set -euo pipefail

if [[ "${CLAUDE_CODE_REMOTE:-}" != 'true' ]]; then
  echo 'This helper is for Anthropic-hosted Claude Code sessions only.' >&2
  exit 2
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
CACHE_ROOT="${TDA_CLAUDE_SETUP_ROOT:-${HOME:?HOME must be set}/.cache/tda-lib-claude-setup}"
PROJECT_DIR="$CACHE_ROOT/project"
STATUS_FILE="$CACHE_ROOT/STATUS.txt"

status_value() {
  local key="$1"
  awk -F= -v key="$key" '$1 == key { sub(/^[^=]*=/, ""); print; exit }' "$STATUS_FILE"
}

verify_prepared_packages() {
  python3 - "$PROJECT_DIR/lake-manifest.json" "$PROJECT_DIR/.lake/packages" <<'PY'
import json
import subprocess
import sys
from pathlib import Path

manifest = json.loads(Path(sys.argv[1]).read_text())
packages_dir = Path(sys.argv[2])
bad = []
for package in manifest["packages"]:
    path = packages_dir / package["name"]
    head = subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"],
        check=False, capture_output=True, text=True,
    )
    dirty = subprocess.run(
        ["git", "-C", str(path), "diff", "--quiet", "HEAD", "--"],
        check=False, capture_output=True,
    )
    staged = subprocess.run(
        ["git", "-C", str(path), "diff", "--cached", "--quiet"],
        check=False, capture_output=True,
    )
    status = subprocess.run(
        ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"],
        check=False, capture_output=True, text=True,
    )
    if (head.returncode or head.stdout.strip() != package["rev"] or
            dirty.returncode or staged.returncode or status.returncode or status.stdout.strip()):
        bad.append(f"{package['name']} expected clean revision {package['rev']}")
if bad:
    print("Prepared package source check failed:", file=sys.stderr)
    print("\n".join(bad), file=sys.stderr)
    raise SystemExit(1)
PY
}

if [[ ! -f "$STATUS_FILE" || ! -f "$PROJECT_DIR/lake-manifest.json" ]]; then
  echo "No prepared tda-lib setup snapshot at $CACHE_ROOT; do not reuse cached dependencies." >&2
  exit 2
fi

for file in lean-toolchain lakefile.toml lake-manifest.json; do
  if ! cmp -s "$ROOT/$file" "$PROJECT_DIR/$file"; then
    echo "Pinned file differs from the prepared snapshot: $file" >&2
    echo 'Do not reuse its dependency sources or oleans; use the checkout pins and report the mismatch.' >&2
    exit 2
  fi
done

lean_status="$(status_value lean_toolchain_status)"
packages_status="$(status_value packages_status)"
cache_status="$(status_value mathlib_cache_status)"
if [[ "$lean_status" != 'ready' ]]; then
  echo "Prepared Lean toolchain is not ready (status: $lean_status). See $STATUS_FILE." >&2
  exit 3
fi

if [[ "$packages_status" == 'ready' ]]; then
  prepared_packages="$PROJECT_DIR/.lake/packages"
  current_packages="$ROOT/.lake/packages"
  if ! verify_prepared_packages; then
    echo 'Prepared dependency sources are missing, dirty, or at the wrong revision; not linking them.' >&2
    exit 3
  fi
  if [[ -L "$current_packages" ]]; then
    target="$(readlink -f "$current_packages" 2>/dev/null || true)"
    if [[ "$target" != "$(readlink -f "$prepared_packages")" ]]; then
      echo "Existing .lake/packages link points elsewhere; left it unchanged: $current_packages" >&2
      exit 4
    fi
  elif [[ -e "$current_packages" ]]; then
    echo "Existing .lake/packages path was left unchanged: $current_packages" >&2
    echo 'Use the checkout-local package sources; no cached path was substituted.' >&2
  else
    mkdir -p "$ROOT/.lake"
    ln -s "$prepared_packages" "$current_packages"
    echo "Linked pinned dependency sources from $prepared_packages"
  fi
else
  echo "Prepared dependency sources are incomplete (status: $packages_status); not linking them." >&2
  exit 3
fi

if [[ "$cache_status" != 'complete' ]]; then
  echo "Mathlib cache is not confirmed complete (status: $cache_status)." >&2
  echo 'Run scripts/bootstrap.sh to fetch/unpack the pinned cache; if it fails, stop before any full build.' >&2
  exit 3
fi

expected_archives="$(status_value mathlib_ltar_count)"
if [[ ! "$expected_archives" =~ ^[0-9]+$ ]] || (( expected_archives == 0 )); then
  echo "The setup status has no verified mathlib archive count: $STATUS_FILE" >&2
  exit 3
fi
prepared_cache_dir="$(status_value mathlib_cache_dir)"
if [[ "$prepared_cache_dir" != "$HOME/.cache/mathlib" ]]; then
  echo "Mathlib cache path differs from the setup snapshot (expected $prepared_cache_dir)." >&2
  exit 3
fi
actual_archives="$(find "$HOME/.cache/mathlib" -type f -name '*.ltar' 2>/dev/null | wc -l | tr -d ' ')"
if [[ ! "$actual_archives" =~ ^[0-9]+$ ]] || (( actual_archives != expected_archives )); then
  echo "Mathlib cache file count changed (setup recorded $expected_archives, found ${actual_archives:-unknown})." >&2
  exit 3
fi
checksum_file="$CACHE_ROOT/mathlib-cache.sha256"
if [[ ! -s "$checksum_file" ]] || \
   [[ "$(wc -l < "$checksum_file" | tr -d ' ')" != "$expected_archives" ]] || \
   ! sha256sum --check --status "$checksum_file"; then
  echo "Mathlib cache archive integrity check failed; see $STATUS_FILE and re-run the pinned bootstrap." >&2
  exit 3
fi

echo 'Pinned setup artifacts match their recorded pins and checksums. Run scripts/bootstrap.sh once in this checkout to revalidate and materialize the mathlib cache.'
