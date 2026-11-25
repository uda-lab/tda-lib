#!/usr/bin/env bash
# Build and run the native erosion fixture (Issue #1063): `RatGradedInput.runErosion` on
# `triangle` against `shiftedTriangle` in degree one, as a compiled executable. Not part of
# scripts/check.sh, the pre-push hook or hosted CI; the default Lake targets do not build it.
#
# Usage: scripts/run-erosion-fixture.sh [--budget SECONDS] [--phases]
#   --budget SECONDS  wall-clock limit for each run (default 1800); an exceeded limit fails.
#   --phases          also print the phase breakdown of the radius 1/2 run (adds one more scan).
#
# Runs radius 0 (the pinned failing witness of `triangle_runErosion_zero`), 49/100 (some
# failure) and 1/2 (pass), prints each outcome and its time, and exits nonzero on any
# mismatch or timeout. The first build compiles the object code of the whole import closure
# (about 3,400 modules, several minutes on four cores); later runs reuse it. The Lean build
# goes through scripts/lean.sh, so it takes the shared build lock. No runtime bound is claimed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

budget=1800
phases=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --budget) [ "$#" -ge 2 ] || { echo "ERROR: --budget needs a value" >&2; exit 64; }
      budget="$2"; shift 2 ;;
    --phases) phases=1; shift ;;
    *) echo "usage: scripts/run-erosion-fixture.sh [--budget SECONDS] [--phases]" >&2; exit 64 ;;
  esac
done
case "$budget" in ''|*[!0-9]*) echo "ERROR: --budget must be a positive integer" >&2; exit 64 ;; esac
[ "$budget" -gt 0 ] || { echo "ERROR: --budget must be a positive integer" >&2; exit 64; }

printf 'host: %s cpus, %s\n' "$(nproc)" \
  "$(sed -n 's/^model name[[:space:]]*:[[:space:]]*//p' /proc/cpuinfo | head -n 1)"

build_start=$(date +%s)
"$ROOT/scripts/lean.sh" lake build erosion-fixture || { echo "ERROR: build failed" >&2; exit 2; }
printf 'build wall time: %s s\n' "$(( $(date +%s) - build_start ))"

exe="$ROOT/.lake/build/bin/erosion-fixture"
[ -x "$exe" ] || { echo "ERROR: $exe not found" >&2; exit 2; }

status=0
run() { # expectation numerator denominator
  local start rc
  start=$(date +%s)
  timeout "$budget" "$exe" lib "$2" "$3" "$1"
  rc=$?
  if [ "$rc" -eq 124 ]; then
    echo "TIMEOUT: radius $2/$3 exceeded ${budget} s" >&2
    status=1
  elif [ "$rc" -ne 0 ]; then
    echo "FAILED: radius $2/$3 exit status $rc" >&2
    status=1
  fi
  printf 'radius %s/%s wall time (incl. process start): %s s\n' "$2" "$3" "$(( $(date +%s) - start ))"
}

run witness0 0 1
run fail 49 100
run pass 1 2
if [ "$phases" -eq 1 ]; then
  timeout "$budget" "$exe" phases 1 2 pass || status=1
fi

if [ "$status" -eq 0 ]; then
  echo "EROSION FIXTURE OK"
else
  echo "EROSION FIXTURE FAILED" >&2
fi
exit "$status"
