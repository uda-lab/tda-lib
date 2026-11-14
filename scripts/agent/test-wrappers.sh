#!/usr/bin/env bash
# Fake executables exercise argv, locking, stop and headroom; no agents are spawned.
set -euo pipefail
SOURCE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir=$(mktemp -d)
trap 'rm -rf -- "$test_dir"' EXIT
mkdir -p "$test_dir/bin" "$test_dir/repo/scripts/lib"
ROOT="$test_dir/repo"
cp "$SOURCE_ROOT/scripts/"{lean.sh,codex.sh} "$ROOT/scripts/"
cp "$SOURCE_ROOT/scripts/lib/"{build-lock.sh,build-resources.py,resources.sh} "$ROOT/scripts/lib/"
printf 'name = "wrapper-fixture"\n' > "$ROOT/lakefile.toml"
cd "$ROOT"
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
cp "$test_dir/bin/lake" "$test_dir/bin/lean"
chmod +x "$test_dir/bin/"*
# Stub CPU-count detection (scripts/lib/resources.sh's lean_detect_num_threads) so the
# unset/no-quota/quota-limited cases below are deterministic regardless of the real machine.
# LEAN_CGROUP_ROOT/LEAN_CGROUP_SELF_PATH replace the real "/sys/fs/cgroup" root and the
# process's own cgroup subpath (normally read from /proc/self/cgroup) with a fixture tree.
cat > "$test_dir/bin/nproc-stub" <<'FAKE'
#!/usr/bin/env bash
printf '%s\n' "${STUB_NPROC:-4}"
FAKE
chmod +x "$test_dir/bin/nproc-stub"
mkdir -p "$test_dir/cg/unlimited" "$test_dir/cg/limited" "$test_dir/cg/nested/child"
printf 'max 100000\n' > "$test_dir/cg/unlimited/cpu.max"
printf '200000 100000\n' > "$test_dir/cg/limited/cpu.max"
# A nested fixture: the process's own (deepest) cgroup has no limit, but its parent does.
printf '200000 100000\n' > "$test_dir/cg/nested/cpu.max"
printf 'max 100000\n' > "$test_dir/cg/nested/child/cpu.max"
export PATH="$test_dir/bin:$PATH" ARGV_OUT="$test_dir/args" LEAN_GUARD_MIN_AVAIL_MIB=0 \
  LEAN_NPROC_CMD="$test_dir/bin/nproc-stub" LEAN_CGROUP_ROOT="$test_dir/cg/unlimited" \
  LEAN_CGROUP_SELF_PATH='' STUB_NPROC=4
"$ROOT/scripts/lean.sh" lake env lean 'space name.lean' '' '*'
python3 - "$ARGV_OUT" <<'PY'
import sys
assert open(sys.argv[1], 'rb').read().split(b'\0')[:-1] == [b'env', b'lean', b'space name.lean', b'', b'*']
PY
if "$ROOT/scripts/lean.sh" lake build -M 4000 >/dev/null 2>&1; then echo 'manual limit accepted'; exit 1; fi
# Unset LEAN_NUM_THREADS, no cgroup quota ("max"): the detected affinity count wins.
[ "$(cat "$ARGV_OUT.threads")" = 4 ]
LEAN_NUM_THREADS=3 "$ROOT/scripts/lean.sh" lake build
# An explicit value is kept exactly, overriding detection.
[ "$(cat "$ARGV_OUT.threads")" = 3 ]
if LEAN_NUM_THREADS=0 "$ROOT/scripts/lean.sh" lake build >/dev/null 2>&1; then
  echo 'invalid thread configuration accepted'; exit 1
fi
# A quota-limited cgroup (ceil(quota/period) below the affinity count) caps detection.
LEAN_CGROUP_ROOT="$test_dir/cg/limited" "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.threads")" = 2 ]
# A cgroup quota above the affinity count never raises it past the detected affinity.
STUB_NPROC=1 LEAN_CGROUP_ROOT="$test_dir/cg/limited" "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.threads")" = 1 ]
# Ancestor shadowing: the process's own (deepest) cgroup has no limit, but a parent's quota is
# stricter. The minimum across every exposed ancestor must win, not just the first readable
# level — a looser/unlimited descendant must not hide a stricter ancestor quota.
STUB_NPROC=8 LEAN_CGROUP_ROOT="$test_dir/cg/nested" LEAN_CGROUP_SELF_PATH=/child \
  "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.threads")" = 2 ]
if "$ROOT/scripts/lean.sh" lake --dir /tmp build >/dev/null 2>&1; then
  echo 'project redirection escaped resource exclusion'; exit 1
fi
if (cd "$test_dir" && "$ROOT/scripts/lean.sh" lake build) >/dev/null 2>&1; then
  echo 'foreign cwd escaped resource exclusion'; exit 1
fi
for tool in lean 'lake env lean'; do
  # Intentional word splitting selects only these fixed tool/subcommand names.
  if "$ROOT/scripts/lean.sh" $tool -o "$test_dir/shared.olean" fixture.lean >/dev/null 2>&1; then
    echo 'external Lean output escaped resource exclusion'; exit 1
  fi
done
"$ROOT/scripts/lean.sh" lean --c="$ROOT/fixture.c" fixture.lean
if "$ROOT/scripts/lean.sh" lean --c="$test_dir/shared.c" fixture.lean >/dev/null 2>&1; then
  echo 'external C output escaped resource exclusion'; exit 1
fi
for form in '--o' '--incr-save'; do
  if "$ROOT/scripts/lean.sh" lean "$form" "$test_dir/shared.out" fixture.lean >/dev/null 2>&1; then
    echo 'separate long output escaped resource exclusion'; exit 1
  fi
done
if "$ROOT/scripts/lean.sh" lean --run -o "$test_dir/shared.olean" fixture.lean >/dev/null 2>&1; then
  echo 'run flag bypassed compiler output checking'; exit 1
fi
# A parent gate and its nested wrapper share the inherited descriptor.
# Watchdog makes a regression fail instead of hanging CI forever.
python3 - "$ROOT" <<'PY_NESTED'
import os, signal, subprocess, sys
process = subprocess.Popen(['bash', '-c',
    'ROOT="$1"; . "$1/scripts/lib/build-lock.sh"; "$1/scripts/lean.sh" lake build',
    '_', sys.argv[1]], start_new_session=True)
try:
    assert process.wait(timeout=5) == 0, 'nested wrapper failed'
except subprocess.TimeoutExpired:
    os.killpg(process.pid, signal.SIGKILL)
    process.wait()
    raise SystemExit('nested wrapper lock timed out')
PY_NESTED
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
