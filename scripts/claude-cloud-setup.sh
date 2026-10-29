#!/usr/bin/env bash
# Paste this file's contents into an Anthropic-hosted Claude Code Setup Script.
# It is intentionally standalone: setup runs before the repository is guaranteed
# to be checked out, and cloud-session environment variables are not available.
set -Eeuo pipefail
umask 022

readonly ELAN_VERSION='4.2.4'
readonly ELAN_ARCHIVE='elan-x86_64-unknown-linux-gnu.tar.gz'
readonly ELAN_SHA256='42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63'
readonly ELAN_URL="https://github.com/leanprover/elan/releases/download/v${ELAN_VERSION}/${ELAN_ARCHIVE}"
readonly LEAN_TOOLCHAIN='leanprover/lean4:v4.33.1'
readonly MATHLIB_TAG='v4.33.1'
readonly MATHLIB_COMMIT='0df444a360eaa60ab8c11dca51a86af692955474'
readonly MAX_SETUP_SECONDS=250

# The override exists for isolated smoke tests. Anthropic setup leaves this unset.
readonly CACHE_ROOT="${TDA_CLAUDE_SETUP_ROOT:-${HOME:?HOME must be set}/.cache/tda-lib-claude-setup}"
readonly PROJECT_DIR="$CACHE_ROOT/project"
readonly LOG_DIR="$CACHE_ROOT/logs"
readonly STATUS_FILE="$CACHE_ROOT/STATUS.txt"
readonly INSTRUCTIONS_FILE="$CACHE_ROOT/INSTRUCTIONS.txt"
readonly CACHE_CHECKSUM_FILE="$CACHE_ROOT/mathlib-cache.sha256"
readonly ELAN_HOME="$HOME/.elan"
readonly MATHLIB_CACHE_DIR="$HOME/.cache/mathlib"
readonly START_EPOCH="$(date +%s)"

ELAN_STATUS='not-attempted'
LEAN_STATUS='not-attempted'
PACKAGES_STATUS='not-attempted'
CACHE_STATUS='not-attempted'
ELAN_VERSION_FOUND='unknown'
ELAN_SECONDS=0
LEAN_SECONDS=0
CACHE_SECONDS=0
CACHE_HASH_SECONDS=0
ELAN_DETAIL='not attempted'
LEAN_DETAIL='not attempted'
PACKAGES_DETAIL='not attempted'
CACHE_DETAIL='not attempted'
CACHE_ARCHIVE_COUNT=0
CACHE_OLEAN_COUNT=0

write_status() {
  local tmp="$STATUS_FILE.tmp"
  local elapsed now state
  now="$(date +%s)"
  elapsed=$((now - START_EPOCH))
  state='partial'
  if [[ "$ELAN_STATUS" == 'ready' && "$LEAN_STATUS" == 'ready' && \
        "$PACKAGES_STATUS" == 'ready' && "$CACHE_STATUS" == 'complete' ]]; then
    state='warm'
  fi
  cat > "$tmp" <<EOF
format=1
state=$state
lean_toolchain=$LEAN_TOOLCHAIN
elan_version_requested=$ELAN_VERSION
elan_version_found=$ELAN_VERSION_FOUND
mathlib_tag=$MATHLIB_TAG
mathlib_commit=$MATHLIB_COMMIT
lean_toolchain_status=$LEAN_STATUS
lean_toolchain_seconds=$LEAN_SECONDS
lean_toolchain_detail=$LEAN_DETAIL
elan_status=$ELAN_STATUS
elan_seconds=$ELAN_SECONDS
elan_detail=$ELAN_DETAIL
packages_status=$PACKAGES_STATUS
packages_detail=$PACKAGES_DETAIL
mathlib_cache_status=$CACHE_STATUS
mathlib_cache_seconds=$CACHE_SECONDS
mathlib_cache_hash_seconds=$CACHE_HASH_SECONDS
mathlib_cache_detail=$CACHE_DETAIL
mathlib_ltar_count=$CACHE_ARCHIVE_COUNT
prepared_olean_count=$CACHE_OLEAN_COUNT
setup_elapsed_seconds=$elapsed
setup_work_budget_seconds=$MAX_SETUP_SECONDS
project_dir=$PROJECT_DIR
mathlib_cache_dir=$MATHLIB_CACHE_DIR
logs_dir=$LOG_DIR
EOF
  mv -f "$tmp" "$STATUS_FILE"
}

write_instructions() {
  cat > "$INSTRUCTIONS_FILE.tmp" <<EOF
This file describes the preparation snapshot; read STATUS.txt for the measured
stage results. A snapshot is fully warm only when state=warm and every stage is
ready/complete. Partial downloads or a partial cache are not a warm cache.

In a fresh tda-lib checkout, run:
  bash scripts/claude-cloud-activate.sh
Then run the repository's normal cache bootstrap:
  bash scripts/bootstrap.sh

The activation helper checks the current lean-toolchain, lakefile.toml, and
lake-manifest.json against this prepared project's exact files before reusing
dependency sources, verifies package revisions and cleanliness, and checks the
saved mathlib archive checksums. Exit 2 or 4 means stop and report a pin/path
conflict. Exit 3 means inspect STATUS.txt: if Lean is ready, bootstrap may
complete the pin-checked cache; if bootstrap fails, stop before a full Lake
build that could cold-build mathlib. Report the failed stage and its log under
logs/.
EOF
  mv -f "$INSTRUCTIONS_FILE.tmp" "$INSTRUCTIONS_FILE"
}

run_bounded() {
  local name="$1" stage_limit="$2" log_file="$3"
  shift 3
  local elapsed remaining allowance started rc
  LAST_STAGE_SECONDS=0
  elapsed=$(( $(date +%s) - START_EPOCH ))
  remaining=$((MAX_SETUP_SECONDS - elapsed))
  allowance="$stage_limit"
  (( allowance > remaining )) && allowance="$remaining"
  if (( allowance <= 0 )); then
    printf '%s: skipped; setup time budget exhausted\n' "$name" > "$log_file"
    printf '%s: skipped (setup time budget exhausted)\n' "$name"
    return 124
  fi
  printf '==> %s (time limit %ss)\n' "$name" "$allowance"
  started="$(date +%s)"
  if timeout --signal=TERM --kill-after=5 "${allowance}s" "$@" > "$log_file" 2>&1; then
    rc=0
  else
    rc=$?
  fi
  LAST_STAGE_SECONDS=$(( $(date +%s) - started ))
  printf '==> %s finished in %ss (exit %s; log %s)\n' \
    "$name" "$LAST_STAGE_SECONDS" "$rc" "$log_file"
  return "$rc"
}

verify_manifest_packages() {
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
    result = subprocess.run(
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
    if (result.returncode or result.stdout.strip() != package["rev"] or
            dirty.returncode or staged.returncode or status.returncode or status.stdout.strip()):
        bad.append(f"{package['name']} expected {package['rev']}")
if bad:
    print("Pinned packages are incomplete or at the wrong revision:", file=sys.stderr)
    print("\n".join(bad), file=sys.stderr)
    raise SystemExit(1)
PY
}

handle_unexpected_error() {
  local rc=$?
  trap - ERR
  if [[ "$ELAN_STATUS" == 'not-attempted' ]]; then ELAN_STATUS='incomplete'; fi
  if [[ "$LEAN_STATUS" == 'not-attempted' ]]; then LEAN_STATUS='blocked'; fi
  if [[ "$PACKAGES_STATUS" == 'not-attempted' ]]; then PACKAGES_STATUS='blocked'; fi
  CACHE_STATUS='incomplete'
  CACHE_DETAIL="setup stopped on an unexpected command failure (exit $rc)"
  write_status 2>/dev/null || true
  write_instructions 2>/dev/null || true
  printf 'Claude cloud setup stopped unexpectedly (exit %s); see %s if it was saved.\n' \
    "$rc" "$STATUS_FILE" >&2
  exit 0
}

if ! mkdir -p "$CACHE_ROOT" "$LOG_DIR" "$PROJECT_DIR" "$MATHLIB_CACHE_DIR"; then
  printf 'Claude cloud setup could not create its cache paths under %s; no cache was prepared.\n' \
    "$CACHE_ROOT" >&2
  exit 0
fi
trap handle_unexpected_error ERR
write_instructions
write_status

missing_tools=()
for tool in curl sha256sum tar timeout git python3 find grep awk; do
  command -v "$tool" >/dev/null 2>&1 || missing_tools+=("$tool")
done
if ((${#missing_tools[@]})); then
  ELAN_STATUS='blocked'
  LEAN_STATUS='blocked'
  PACKAGES_STATUS='blocked'
  CACHE_STATUS='blocked'
  ELAN_DETAIL="missing utilities: ${missing_tools[*]}"
  LEAN_DETAIL='blocked by missing utilities'
  PACKAGES_DETAIL='blocked by missing utilities'
  CACHE_DETAIL='blocked by missing utilities'
  write_status
  printf 'Claude cloud setup is partial (%s). See %s\n' \
    "$ELAN_DETAIL" "$STATUS_FILE"
  exit 0
fi

export ELAN_HOME
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$ELAN_HOME"

ELAN_STAGE_STARTED="$(date +%s)"
if [[ -x "$ELAN_HOME/bin/elan" ]]; then
  if ELAN_VERSION_FOUND="$("$ELAN_HOME/bin/elan" --version 2>&1)" &&
     [[ "$ELAN_VERSION_FOUND" == "elan $ELAN_VERSION"* ]]; then
    ELAN_STATUS='ready'
    ELAN_DETAIL='reused the existing pinned Elan installation'
  else
    ELAN_STATUS='blocked'
    ELAN_DETAIL="existing Elan differs from pinned v$ELAN_VERSION; left untouched"
  fi
else
  archive="$CACHE_ROOT/downloads/$ELAN_ARCHIVE"
  mkdir -p "$(dirname "$archive")"
  if [[ -f "$archive" ]] && printf '%s  %s\n' "$ELAN_SHA256" "$archive" | \
      sha256sum --check --status -; then
    printf '==> Reusing verified Elan archive %s\n' "$archive"
  else
    part="$archive.part"
    if run_bounded 'elan archive download' 35 "$LOG_DIR/elan-download.log" \
        curl --fail --location --silent --show-error --connect-timeout 10 \
        --max-time 35 --retry 1 --retry-delay 1 --output "$part" "$ELAN_URL"; then
      :
    else
      rc=$?
      ELAN_STATUS='incomplete'
      ELAN_DETAIL="archive download failed or timed out (exit $rc)"
    fi
    if [[ -f "$part" ]]; then
      if printf '%s  %s\n' "$ELAN_SHA256" "$part" | sha256sum --check --status -; then
        mv -f "$part" "$archive"
      else
        rm -f "$part"
        ELAN_STATUS='incomplete'
        ELAN_DETAIL='Elan archive checksum did not match the pinned release digest'
      fi
    fi
  fi
  if [[ -f "$archive" ]] && printf '%s  %s\n' "$ELAN_SHA256" "$archive" | \
      sha256sum --check --status -; then
    unpack_dir="$CACHE_ROOT/tmp/elan-unpack"
    mkdir -p "$unpack_dir"
    if run_bounded 'elan archive extraction' 10 "$LOG_DIR/elan-extract.log" \
        tar -xzf "$archive" -C "$unpack_dir"; then
      if [[ -x "$unpack_dir/elan-init" ]] && \
         run_bounded 'elan installation' 25 "$LOG_DIR/elan-install.log" \
           env ELAN_HOME="$ELAN_HOME" "$unpack_dir/elan-init" -y \
             --no-modify-path --default-toolchain none; then
        if [[ -x "$ELAN_HOME/bin/elan" ]] && \
           ELAN_VERSION_FOUND="$("$ELAN_HOME/bin/elan" --version 2>&1)" && \
           [[ "$ELAN_VERSION_FOUND" == "elan $ELAN_VERSION"* ]]; then
          ELAN_STATUS='ready'
          ELAN_DETAIL='installed the checksum-verified pinned Elan release'
        else
          ELAN_STATUS='incomplete'
          ELAN_DETAIL='elan-init completed but the pinned elan binary did not verify'
        fi
      else
        ELAN_STATUS='incomplete'
        ELAN_DETAIL='elan-init was missing or failed; see logs/elan-install.log'
      fi
    else
      ELAN_STATUS='incomplete'
      ELAN_DETAIL='Elan archive extraction failed; see logs/elan-extract.log'
    fi
  fi
fi
ELAN_SECONDS=$(( $(date +%s) - ELAN_STAGE_STARTED ))
write_status

LEAN_STAGE_STARTED="$(date +%s)"
if [[ "$ELAN_STATUS" == 'ready' ]]; then
  if "$ELAN_HOME/bin/elan" toolchain list 2>/dev/null | \
      awk -v wanted="$LEAN_TOOLCHAIN" '$1 == wanted { found = 1 } END { exit !found }'; then
    LEAN_STATUS='checking'
    LEAN_DETAIL='found the exact toolchain registration; verifying Lean and Lake binaries'
  elif run_bounded 'Lean toolchain install' 115 "$LOG_DIR/lean-toolchain.log" \
      "$ELAN_HOME/bin/elan" toolchain install "$LEAN_TOOLCHAIN"; then
    LEAN_STATUS='checking'
    LEAN_DETAIL='toolchain install returned success; verifying Lean and Lake binaries'
  else
    rc=$?
    LEAN_STATUS='incomplete'
    LEAN_DETAIL="toolchain install failed or timed out (exit $rc)"
  fi
  if [[ "$LEAN_STATUS" == 'checking' ]]; then
    if run_bounded 'Lean/Lake version verification' 10 "$LOG_DIR/lean-version.log" \
        bash -c '"$1" run "$2" lean --version && "$1" run "$2" lake --version' \
          _ "$ELAN_HOME/bin/elan" "$LEAN_TOOLCHAIN"; then
      if grep -Fq 'Lean (version 4.33.1,' "$LOG_DIR/lean-version.log" && \
         grep -Fq '(Lean version 4.33.1)' "$LOG_DIR/lean-version.log"; then
        LEAN_STATUS='ready'
        LEAN_DETAIL='Lean and Lake binaries both verified as 4.33.1'
      else
        LEAN_STATUS='incomplete'
        LEAN_DETAIL='Lean/Lake version output did not match 4.33.1; see logs/lean-version.log'
      fi
    else
      rc=$?
      LEAN_STATUS='incomplete'
      LEAN_DETAIL="Lean/Lake verification failed or timed out (exit $rc)"
    fi
  fi
  LEAN_SECONDS=$(( $(date +%s) - LEAN_STAGE_STARTED ))
else
  LEAN_STATUS='blocked'
  LEAN_DETAIL='blocked because the pinned Elan install is unavailable'
fi
write_status

# This exact project copy makes cache downloads independent of checkout paths and
# repository credentials. Keep the embedded files in sync with the tracked pins.
cat > "$PROJECT_DIR/lean-toolchain" <<'TDA_LEAN_TOOLCHAIN'
leanprover/lean4:v4.33.1
TDA_LEAN_TOOLCHAIN
cat > "$PROJECT_DIR/lakefile.toml" <<'TDA_LAKEFILE'
name = "TDA"
version = "0.3.0"
description = "Lean 4 formalizations of topological data analysis, with verified finite persistent homology computation."
keywords = ["math", "topology", "topological-data-analysis", "persistent-homology", "software-verification"]
license = "Apache-2.0"
defaultTargets = ["TDA"]

[leanOptions]
autoImplicit = false   # an unbound variable must be an error, never a silent ∀

# The tag selects the mathlib release; the resolved commit is pinned in lake-manifest.json.
# Bumping either is an infrastructure Issue, never a side effect of other work.
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.33.1"

[[lean_lib]]
name = "TDA"
TDA_LAKEFILE
cat > "$PROJECT_DIR/lake-manifest.json" <<'TDA_LAKE_MANIFEST'
{"version": "1.2.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/mathlib4.git",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "0df444a360eaa60ab8c11dca51a86af692955474",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.33.1",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/plausible",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "b7eb3304aeae834b12dda98993a37f6a41f6f0bb",
   "name": "plausible",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/LeanSearchClient",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "5f4d51b81cbd3f6b32b156bfad9056621a040404",
   "name": "LeanSearchClient",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/import-graph",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "16f02aa7642864af59f1ff0e384a015994db9118",
   "name": "importGraph",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/ProofWidgets4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "4be2e3d5087eeb272cf5a8853b8f9dd025ef5957",
   "name": "proofwidgets",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/aesop",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "3448c0bcc5ce01b2d1546e483ec3620e32df3d0e",
   "name": "aesop",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/quote4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "92c15be17b7caf78c2ad767ec40f89052d908d81",
   "name": "Qq",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover/lean4-cli",
   "type": "git",
   "subDir": null,
   "scope": "leanprover",
   "rev": "6130a47896ce867c6a4a55373441e59e565bad0f",
   "name": "Cli",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.33.0",
   "inherited": true,
   "configFile": "lakefile.toml"}],
 "name": "TDA",
 "lakeDir": ".lake",
 "fixedToolchain": false}
TDA_LAKE_MANIFEST

if [[ "$LEAN_STATUS" == 'ready' ]]; then
  export LEAN_NUM_THREADS=1
  export MATHLIB_CACHE_DIR
  mkdir -p "$PROJECT_DIR/.lake"
  if run_bounded 'pinned mathlib cache get' 210 "$LOG_DIR/mathlib-cache.log" \
      bash -c 'cd "$1" && "$2" exe cache get' _ "$PROJECT_DIR" "$ELAN_HOME/bin/lake"; then
    CACHE_SECONDS="$LAST_STAGE_SECONDS"
    if verify_manifest_packages > "$LOG_DIR/package-revisions.log" 2>&1; then
      PACKAGES_STATUS='ready'
      PACKAGES_DETAIL='all packages are checked out at the lake-manifest.json commits'
    else
      PACKAGES_STATUS='incomplete'
      PACKAGES_DETAIL='one or more packages are missing, dirty, or do not match the manifest'
    fi
    CACHE_ARCHIVE_COUNT="$(find "$MATHLIB_CACHE_DIR" -type f -name '*.ltar' 2>/dev/null | wc -l | tr -d ' ')"
    CACHE_OLEAN_COUNT="$(find "$PROJECT_DIR/.lake" -type f -name '*.olean' 2>/dev/null | wc -l | tr -d ' ')"
    if [[ "$PACKAGES_STATUS" == 'ready' && "$CACHE_ARCHIVE_COUNT" -gt 0 ]] && \
       ! grep -Eq 'Warning: some files were not found|download\(s\) failed|Downloading .* files failed|No container URLs configured' "$LOG_DIR/mathlib-cache.log"; then
      if run_bounded 'mathlib cache checksum manifest' 20 "$LOG_DIR/mathlib-cache-checksum.log" \
          bash -c 'set -euo pipefail; find "$1" -type f -name "*.ltar" -print0 | sort -z | xargs -0 sha256sum > "$2"' \
            _ "$MATHLIB_CACHE_DIR" "$CACHE_CHECKSUM_FILE.tmp"; then
        CACHE_HASH_SECONDS="$LAST_STAGE_SECONDS"
        checksum_count="$(wc -l < "$CACHE_CHECKSUM_FILE.tmp" | tr -d ' ')"
        if [[ "$checksum_count" == "$CACHE_ARCHIVE_COUNT" && "$checksum_count" -gt 0 ]]; then
          mv -f "$CACHE_CHECKSUM_FILE.tmp" "$CACHE_CHECKSUM_FILE"
          CACHE_STATUS='complete'
          CACHE_DETAIL='cache command succeeded without misses and every archive has a checksum'
        else
          rm -f "$CACHE_CHECKSUM_FILE.tmp"
          CACHE_STATUS='incomplete'
          CACHE_DETAIL='cache archive checksum manifest did not cover every archive'
        fi
      else
        rc=$?
        CACHE_HASH_SECONDS="${LAST_STAGE_SECONDS:-0}"
        rm -f "$CACHE_CHECKSUM_FILE.tmp"
        CACHE_STATUS='incomplete'
        CACHE_DETAIL="cache checksum manifest failed or timed out (exit $rc)"
      fi
    else
      CACHE_STATUS='incomplete'
      CACHE_DETAIL='cache was partial or could not be confirmed complete; see logs/mathlib-cache.log'
    fi
  else
    rc=$?
    CACHE_SECONDS="${LAST_STAGE_SECONDS:-0}"
    CACHE_STATUS='incomplete'
    CACHE_DETAIL="cache get failed, missed artifacts, or timed out (exit $rc); see logs/mathlib-cache.log"
    if verify_manifest_packages > "$LOG_DIR/package-revisions.log" 2>&1; then
      PACKAGES_STATUS='ready'
      PACKAGES_DETAIL='all packages are checked out at the lake-manifest.json commits despite cache failure'
    else
      PACKAGES_STATUS='incomplete'
      PACKAGES_DETAIL='one or more packages are missing, dirty, or do not match the manifest'
    fi
    CACHE_ARCHIVE_COUNT="$(find "$MATHLIB_CACHE_DIR" -type f -name '*.ltar' 2>/dev/null | wc -l | tr -d ' ')"
    CACHE_OLEAN_COUNT="$(find "$PROJECT_DIR/.lake" -type f -name '*.olean' 2>/dev/null | wc -l | tr -d ' ')"
  fi
else
  PACKAGES_STATUS='blocked'
  CACHE_STATUS='blocked'
  PACKAGES_DETAIL='blocked because the exact Lean toolchain is unavailable'
  CACHE_DETAIL='blocked because the exact Lean toolchain is unavailable'
fi

write_status
write_instructions
printf 'Claude cloud setup state: %s\n' \
  "$(sed -n 's/^state=//p' "$STATUS_FILE")"
printf 'Status: %s\nInstructions: %s\nLogs: %s\n' \
  "$STATUS_FILE" "$INSTRUCTIONS_FILE" "$LOG_DIR"
printf 'Stages: elan=%s lean=%s packages=%s mathlib-cache=%s\n' \
  "$ELAN_STATUS" "$LEAN_STATUS" "$PACKAGES_STATUS" "$CACHE_STATUS"
exit 0
