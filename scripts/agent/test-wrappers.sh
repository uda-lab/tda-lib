#!/usr/bin/env bash
# Fake executables exercise argv, locking, stop and headroom; no agents are spawned.
set -euo pipefail
SOURCE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir=$(mktemp -d)
trap 'rm -rf -- "$test_dir"' EXIT
mkdir -p "$test_dir/bin" "$test_dir/repo/scripts/lib"
ROOT="$test_dir/repo"
cp "$SOURCE_ROOT/scripts/"{lean.sh,codex.sh,bootstrap.sh} "$ROOT/scripts/"
cp "$SOURCE_ROOT/scripts/lib/"{build-lock.sh,build-resources.py,resources.sh,lake-artifact-cache.sh} "$ROOT/scripts/lib/"
printf 'name = "wrapper-fixture"\n' > "$ROOT/lakefile.toml"
mkdir -p "$ROOT/docbuild"
printf 'name = "wrapper-docbuild-fixture"\n' > "$ROOT/docbuild/lakefile.toml"
git init -q "$ROOT"
cd "$ROOT"
cat > "$test_dir/bin/lake" <<'FAKE'
#!/usr/bin/env bash
printf '%s\0' "$@" > "$ARGV_OUT"
printf '%s' "${LEAN_NUM_THREADS:-unset}" > "$ARGV_OUT.threads"
printf '%s' "${LEAN_NUM_THREADS_SOURCE:-unset}" > "$ARGV_OUT.source"
printf '%s' "${LEAN_NUM_THREADS_DETECTED:-unset}" > "$ARGV_OUT.detected"
printf '%s' "${LAKE_ARTIFACT_CACHE-unset}" > "$ARGV_OUT.artifact-cache"
printf '%s' "${LAKE_RESTORE_ARTIFACTS-unset}" > "$ARGV_OUT.restore-artifacts"
printf '%s' "${LAKE_CACHE_DIR-unset}" > "$ARGV_OUT.cache-dir"
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
  LEAN_CGROUP_SELF_PATH='' STUB_NPROC=6
unset LAKE_ARTIFACT_CACHE LAKE_RESTORE_ARTIFACTS LAKE_CACHE_DIR
"$ROOT/scripts/lean.sh" lake env lean 'space name.lean' '' '*'
python3 - "$ARGV_OUT" <<'PY'
import sys
assert open(sys.argv[1], 'rb').read().split(b'\0')[:-1] == [b'env', b'lean', b'space name.lean', b'', b'*']
PY
[ "$(cat "$ARGV_OUT.artifact-cache")" = true ]
[ "$(cat "$ARGV_OUT.restore-artifacts")" = true ]
python3 - "$ROOT" "$(cat "$ARGV_OUT.cache-dir")" <<'PY'
from pathlib import Path
import sys
root, cache = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
assert root not in cache.parents and cache != root
PY
if "$ROOT/scripts/lean.sh" lake build -M 4000 >/dev/null 2>&1; then echo 'manual limit accepted'; exit 1; fi
# Unset LEAN_NUM_THREADS, no cgroup quota ("max"): stays at the single-thread fallback, but the
# detected affinity count (6) is still reported for visibility.
[ "$(cat "$ARGV_OUT.threads")" = 1 ]
[ "$(cat "$ARGV_OUT.source")" = fallback ]
[ "$(cat "$ARGV_OUT.detected")" = 6 ]
LEAN_NUM_THREADS=3 "$ROOT/scripts/lean.sh" lake build
# An explicit value is kept exactly, overriding the fallback; detection still runs and is
# reported, but does not affect the explicit value.
[ "$(cat "$ARGV_OUT.threads")" = 3 ]
[ "$(cat "$ARGV_OUT.source")" = explicit ]
[ "$(cat "$ARGV_OUT.detected")" = 6 ]
LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=true "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.artifact-cache")" = false ]
[ "$(cat "$ARGV_OUT.restore-artifacts")" = true ]
LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=false "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.artifact-cache")" = true ]
[ "$(cat "$ARGV_OUT.restore-artifacts")" = false ]
env -u LAKE_ARTIFACT_CACHE -u LAKE_RESTORE_ARTIFACTS -u LAKE_CACHE_DIR "$ROOT/scripts/bootstrap.sh"
python3 - "$ARGV_OUT" <<'PY'
import sys
args = open(sys.argv[1], 'rb').read().split(b'\0')[:-1]
assert args == [b'exe', b'cache', b'get']
assert open(sys.argv[1] + '.artifact-cache').read() == 'true'
assert open(sys.argv[1] + '.restore-artifacts').read() == 'true'
PY
LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false "$ROOT/scripts/bootstrap.sh"
[ "$(cat "$ARGV_OUT.artifact-cache")" = false ]
[ "$(cat "$ARGV_OUT.restore-artifacts")" = false ]
if LEAN_NUM_THREADS=0 "$ROOT/scripts/lean.sh" lake build >/dev/null 2>&1; then
  echo 'invalid thread configuration accepted'; exit 1
fi
# A quota-limited cgroup (ceil(quota/period) below the affinity count) caps the DETECTED value
# (quota 2, affinity 6 -> 2); the thread count used still stays at the fallback of 1.
LEAN_CGROUP_ROOT="$test_dir/cg/limited" "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.threads")" = 1 ]
[ "$(cat "$ARGV_OUT.detected")" = 2 ]
# A cgroup quota above the affinity count never raises detection past the detected affinity:
# affinity 1, quota 2 -> detected 1.
STUB_NPROC=1 LEAN_CGROUP_ROOT="$test_dir/cg/limited" "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.threads")" = 1 ]
[ "$(cat "$ARGV_OUT.detected")" = 1 ]
# Ancestor shadowing: the process's own (deepest) cgroup has no limit, but a parent's quota is
# stricter. The minimum across every exposed ancestor must win, not just the first readable
# level — a looser/unlimited descendant must not hide a stricter ancestor quota. Affinity 8,
# ancestor quota 2 -> detected 2; the thread count used still stays at the fallback of 1.
STUB_NPROC=8 LEAN_CGROUP_ROOT="$test_dir/cg/nested" LEAN_CGROUP_SELF_PATH=/child \
  "$ROOT/scripts/lean.sh" lake build
[ "$(cat "$ARGV_OUT.threads")" = 1 ]
[ "$(cat "$ARGV_OUT.detected")" = 2 ]
if "$ROOT/scripts/lean.sh" lake --dir /tmp build >/dev/null 2>&1; then
  echo 'project redirection escaped resource exclusion'; exit 1
fi
if (cd "$test_dir" && "$ROOT/scripts/lean.sh" lake build) >/dev/null 2>&1; then
  echo 'foreign cwd escaped resource exclusion'; exit 1
fi
# A parent guard starts at the repository root, then its nested Lake wrapper runs in docbuild.
# An explicit relative cache path must be normalized once so the nested lock set matches.
python3 - "$ROOT" "$ARGV_OUT" <<'PY'
import os, subprocess, sys
from pathlib import Path
root, argv_out = Path(sys.argv[1]), sys.argv[2]
env = os.environ.copy()
env['LAKE_CACHE_DIR'] = '../shared-cache'
command = ['bash', '-c',
    'ROOT="$1"; . "$1/scripts/lib/build-lock.sh"; cd "$1/docbuild"; '
    '"$1/scripts/lean.sh" lake build', '_', str(root)]
result = subprocess.run(command, env=env, capture_output=True, text=True)
assert result.returncode == 0, result.stderr
actual = Path(open(argv_out + '.cache-dir').read()).resolve()
assert actual == (root.parent / 'shared-cache').resolve(), actual
PY
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
