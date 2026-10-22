#!/usr/bin/env bash
# Fake executables exercise argv, locking, stop and headroom; no agents are spawned.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir=$(mktemp -d)
trap 'rm -rf -- "$test_dir"' EXIT
mkdir "$test_dir/bin"
cat > "$test_dir/bin/lake" <<'FAKE'
#!/usr/bin/env bash
printf '%s\0' "$@" > "$ARGV_OUT"
printf '%s' "${LEAN_NUM_THREADS:-unset}" > "$ARGV_OUT.threads"
if [ -n "${SERIAL_OUT:-}" ]; then
 printf 'start\n' >> "$SERIAL_OUT"
 sleep .15
 printf 'end\n' >> "$SERIAL_OUT"
fi
FAKE
cp "$test_dir/bin/lake" "$test_dir/bin/codex"
chmod +x "$test_dir/bin/"*
export PATH="$test_dir/bin:$PATH" ARGV_OUT="$test_dir/args" LEAN_GUARD_MIN_AVAIL_MIB=0
"$ROOT/scripts/lean.sh" lake env lean 'space name.lean' '' '*'
python3 - "$ARGV_OUT" <<'PY'
import sys
assert open(sys.argv[1], 'rb').read().split(b'\0')[:-1] == [b'env', b'lean', b'space name.lean', b'', b'*']
PY
if "$ROOT/scripts/lean.sh" lake build -M 4000 >/dev/null 2>&1; then echo 'manual limit accepted'; exit 1; fi
[ "$(cat "$ARGV_OUT.threads")" = 1 ]
LEAN_NUM_THREADS=3 "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.threads")" = 3 ]
if LEAN_NUM_THREADS=0 "$ROOT/scripts/lean.sh" lake build >/dev/null 2>&1; then
  echo 'invalid thread configuration accepted'; exit 1
fi
if "$ROOT/scripts/lean.sh" lake --dir /tmp build >/dev/null 2>&1; then
  echo 'project redirection escaped resource exclusion'; exit 1
fi
if (cd "$test_dir" && "$ROOT/scripts/lean.sh" lake build) >/dev/null 2>&1; then
  echo 'foreign cwd escaped resource exclusion'; exit 1
fi
# A parent gate and its nested wrapper share the inherited descriptor.
# Watchdog makes a regression fail instead of hanging CI forever.
bash -c 'ROOT="$1"; . "$1/scripts/lib/build-lock.sh"; "$1/scripts/lean.sh" lake build' _ "$ROOT" & nested=$!
(sleep 5; kill "$nested" 2>/dev/null || :) & watchdog=$!
if wait "$nested"; then
  kill "$watchdog" 2>/dev/null || :
  wait "$watchdog" 2>/dev/null || :
else
  kill "$watchdog" 2>/dev/null || :
  wait "$watchdog" 2>/dev/null || :
  echo 'nested wrapper lock failed'; exit 1
fi
export SERIAL_OUT="$test_dir/serial"
"$ROOT/scripts/lean.sh" lake build & first=$!
"$ROOT/scripts/lean.sh" lake build & second=$!
wait "$first"; wait "$second"
[ "$(cat "$SERIAL_OUT")" = $'start\nend\nstart\nend' ]
unset SERIAL_OUT
export CODEX_STOP_FILE="$test_dir/stop" LOOP_JOB_ID=TDA/issue-3/worker
"$ROOT/scripts/codex.sh" exec 'space prompt' ''
python3 - "$ARGV_OUT" <<'PY'
import sys
assert open(sys.argv[1], 'rb').read().split(b'\0')[:-1] == [b'exec', b'space prompt', b'']
PY
touch "$CODEX_STOP_FILE"
if "$ROOT/scripts/lean.sh" lake build >/dev/null 2>&1; then echo 'Lean stop ignored'; exit 1; fi
if "$ROOT/scripts/codex.sh" exec test >/dev/null 2>&1; then echo 'stop ignored'; exit 1; fi
rm "$CODEX_STOP_FILE"
if LOOP_JOB_ID='' "$ROOT/scripts/codex.sh" exec test >/dev/null 2>&1; then echo 'missing ownership accepted'; exit 1; fi
if [ -r /proc/meminfo ]; then
 if LEAN_GUARD_MIN_AVAIL_MIB=99999999 "$ROOT/scripts/lean.sh" lake build >/dev/null 2>&1; then echo 'headroom ignored'; exit 1; fi
fi
echo 'wrapper self-tests OK'
