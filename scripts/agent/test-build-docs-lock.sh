#!/usr/bin/env bash
set -euo pipefail

# Fixture repositories must not join a caller's real cache or inherited lock set.
unset LAKE_CACHE_DIR LAKE_ARTIFACT_CACHE LAKE_RESTORE_ARTIFACTS LEAN_RESOURCE_LOCK_FDS

fenv() { env -u GIT_DIR -u GIT_WORK_TREE -u GIT_INDEX_FILE GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 "$@"; }
fgit() { fenv git "$@"; }
frun() { fenv env "$@"; }

SOURCE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d /tmp/tda-build-docs-lock.XXXXXX)"
first=""
second=""
holder=""
stopped=""
stop_file="$tmp/codex-stop"
release="$tmp/release-lock"
cancel_file="$tmp/cancel-builds"
cleanup() {
  local result=$?
  trap - EXIT
  set +e
  touch "$stop_file" "$cancel_file"
  touch "$release"
  for pid in "$holder" "$first" "$second" "$stopped"; do
    [ -n "$pid" ] && wait "$pid" 2>/dev/null
  done
  if [ -n "${LOCK:-}" ] && ! flock -w 5 -n "$LOCK" true 2>/dev/null; then
    echo 'test cleanup could not confirm the shared build lock was released' >&2
    result=1
  fi
  rm -rf -- "$tmp"
  exit "$result"
}
trap cleanup EXIT
fixture="$tmp/repo"
mkdir -p "$fixture/scripts/lib" "$fixture/docbuild/.lake/build/doc-data" \
  "$fixture/docbuild/.lake/build/doc/TDA" "$fixture/docbuild/.lake/build/doc/declarations" \
  "$tmp/bin"
# Portable fixture-only flock adapter; production supports flock or Perl.
cat > "$tmp/bin/flock" <<'EOF'
#!/usr/bin/env python3
import fcntl, os, subprocess, sys, time
args = sys.argv[1:]
nonblock = False
shared = False
deadline = None
while args and args[0].startswith('-'):
    flag = args.pop(0)
    if flag == '-n': nonblock = True
    elif flag == '-s': shared = True
    elif flag == '-w': deadline = time.monotonic() + float(args.pop(0))
    else: sys.exit(64)
target = args.pop(0)
watch = False
if target.isdigit():
    fd = int(target)
    if os.environ.get('WATCH_LOCK_ATTEMPTS'):
        held = os.fstat(fd)
        watched = os.stat(os.environ['WATCH_LOCK_TARGET'])
        watch = (held.st_dev, held.st_ino) == (watched.st_dev, watched.st_ino)
else:
    fd = os.open(target, os.O_WRONLY | os.O_CREAT, 0o600)
while True:
    try:
        fcntl.flock(fd, (fcntl.LOCK_SH if shared else fcntl.LOCK_EX) | (fcntl.LOCK_NB if nonblock or deadline or watch else 0))
        break
    except BlockingIOError:
        if watch:
            # Signal only an observed conflict on the lock held by this fixture.
            open(os.environ['WATCH_LOCK_ATTEMPTS'], 'a').close()
        if nonblock or (deadline is not None and time.monotonic() >= deadline): sys.exit(1)
        time.sleep(.01)
if args: sys.exit(subprocess.call(args))
EOF
chmod +x "$tmp/bin/flock"
export PATH="$tmp/bin:$PATH"
cp "$SOURCE_ROOT/scripts/build-docs.sh" "$fixture/scripts/build-docs.sh"
cp "$SOURCE_ROOT/scripts/lib/"build-{lock.sh,resources.py} \
  "$SOURCE_ROOT/scripts/lib/resources.sh" "$SOURCE_ROOT/scripts/lib/lake-artifact-cache.sh" \
  "$fixture/scripts/lib/"
cp "$SOURCE_ROOT/scripts/lib/docs-cache.py" "$fixture/scripts/lib/"
for file in lean-toolchain lakefile.toml lake-manifest.json docbuild/lean-toolchain docbuild/lake-manifest.json; do
  cp "$SOURCE_ROOT/$file" "$fixture/$file"
done
LOCK=$(python3 "$fixture/scripts/lib/build-resources.py" --root-lock "$fixture")
export LOCK
if [ -n "${TEST_CLEANUP_LOCK_REPORT:-}" ]; then
  printf '%s\n' "$LOCK" > "$TEST_CLEANUP_LOCK_REPORT"
fi
chmod +x "$fixture/scripts/build-docs.sh"
cat > "$fixture/.gitignore" <<'EOF'
/docbuild/.lake/
EOF
cat > "$fixture/docbuild/lakefile.toml" <<'EOF'
name = "lock-test"
EOF
fgit -C "$fixture" init -q
fgit -C "$fixture" config user.name "Lock Test"
fgit -C "$fixture" config user.email "lock-test@example.invalid"
export TEST_ROOT="$fixture"
export TEST_EVENTS="$tmp/events"
: > "$TEST_EVENTS"
cat > "$fixture/scripts/lean.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
fenv() { env -u GIT_DIR -u GIT_WORK_TREE -u GIT_INDEX_FILE GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 "$@"; }
fgit() { fenv git "$@"; }
ROOT="$TEST_ROOT"
. "$TEST_ROOT/scripts/lib/build-lock.sh"
[[ "$PWD" == "$TEST_ROOT/docbuild" ]]
[[ "$#" -eq 3 && "$1" == lake && "$2" == build && "$3" == +TDA.Library:docs ]]
run_index="$(grep -c '^lean-start ' "$TEST_EVENTS" || true)"
run_index=$((run_index + 1))
doc_root="$TEST_ROOT/docbuild/.lake/build/doc"
source_rev_file="$TEST_ROOT/docbuild/.lake/docs-source-rev"
if [ "${TEST_FAIL_LEAN:-0}" = 1 ]; then
  printf 'lean-start %s\n' "$run_index" >> "$TEST_EVENTS"
  exit 42
fi
if [ "$run_index" -eq 1 ]; then
  [[ ! -e "$doc_root/TDA/stale" ]]
elif [ "$run_index" -eq 2 ] && [ "${TEST_FAIL_DOC_LOCK_CHECK:-0}" = 0 ]; then
  expected_rev="$(fgit -C "$TEST_ROOT" rev-parse HEAD)"
  [[ "$(cat "$source_rev_file")" == "$expected_rev" ]]
  [[ "$(cat "$doc_root/TDA/generated")" == generated-1 ]]
fi
printf 'lean-start %s\n' "$run_index" >> "$TEST_EVENTS"
sleep 0.25
mkdir -p "$doc_root/TDA"
touch "$doc_root/index.html"
printf 'generated-%s\n' "$run_index" > "$doc_root/TDA/generated"
printf 'lean-end %s\n' "$run_index" >> "$TEST_EVENTS"
EOF
chmod +x "$fixture/scripts/lean.sh"
cat > "$fixture/scripts/check-doc-lock.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[ -n "${LEAN_RESOURCE_LOCK_FDS:-}" ]
if flock -n "$LOCK" true 2>/dev/null; then
  echo 'resource lock was not held through dependency verification' >&2
  exit 1
fi
[[ -f "$TEST_ROOT/docbuild/.lake/build/doc/TDA/generated" ]]
run_index="$(grep -c '^check-start ' "$TEST_EVENTS" || true)"
run_index=$((run_index + 1))
printf 'check-start %s\n' "$run_index" >> "$TEST_EVENTS"
if [ "${TEST_FAIL_DOC_LOCK_CHECK:-0}" = 1 ]; then
  exit 43
fi
sleep 0.25
printf 'check-end %s\n' "$run_index" >> "$TEST_EVENTS"
EOF
chmod +x "$fixture/scripts/check-doc-lock.sh"
fgit -C "$fixture" add .gitignore lean-toolchain lakefile.toml lake-manifest.json docbuild scripts
fgit -C "$fixture" commit -qm "fixture"

printf 'stale-revision\n' > "$fixture/docbuild/.lake/docs-source-rev"
touch "$fixture/docbuild/.lake/build/doc-data/TDA.stale" \
  "$fixture/docbuild/.lake/build/doc/TDA/stale" \
  "$fixture/docbuild/.lake/build/doc/TDA.html" \
  "$fixture/docbuild/.lake/build/doc/declarations/declaration-data.bmp"
if [ -n "$(fgit -C "$fixture" status --porcelain --untracked-files=all)" ]; then
  fgit -C "$fixture" status --short --untracked-files=all >&2
  exit 1
fi
# The parent covers every normal transaction. Cleanup children start at the owned-lock
# scenario below so their 20s deadline measures that scenario, not a repeated full suite.
if [ "${TEST_CLEANUP_CHILD:-0}" != 1 ]; then
# Bound each test-owned builder so cleanup can finish if another process owns the shared lock.
frun CODEX_STOP_FILE="$cancel_file" timeout --kill-after=2s 10s \
  "$fixture/scripts/build-docs.sh" > "$tmp/first.log" 2>&1 & first=$!
for _ in $(seq 1 500); do
  if grep -q '^lean-start ' "$TEST_EVENTS" 2>/dev/null; then break; fi
  kill -0 "$first" 2>/dev/null || { cat "$tmp/first.log" >&2; exit 1; }
  sleep 0.01
done
grep -q '^lean-start ' "$TEST_EVENTS" || { echo 'first documentation build did not start' >&2; exit 1; }
printf 'second-launched\n' >> "$TEST_EVENTS"
frun CODEX_STOP_FILE="$cancel_file" timeout --kill-after=2s 10s \
  "$fixture/scripts/build-docs.sh" > "$tmp/second.log" 2>&1 & second=$!
wait "$first" || { cat "$tmp/first.log" >&2; exit 1; }
wait "$second" || { cat "$tmp/second.log" >&2; exit 1; }
python3 - "$TEST_EVENTS" <<'PY'
import sys
events = [line.split()[0] for line in open(sys.argv[1])]
expected = [
    "lean-start", "second-launched", "lean-end", "check-start", "check-end",
    "lean-start", "lean-end", "check-start", "check-end",
]
if events != expected:
    raise SystemExit(f"documentation transactions overlapped or reordered: {events}")
PY
expected_rev="$(fgit -C "$fixture" rev-parse HEAD)"
[[ "$(cat "$fixture/docbuild/.lake/docs-source-rev")" == "$expected_rev" ]]

# Failed generation or dependency verification must not record the current revision as documented.
: > "$TEST_EVENTS"
printf 'pre-failure-revision\n' > "$fixture/docbuild/.lake/docs-source-rev"
if frun TEST_FAIL_LEAN=1 "$fixture/scripts/build-docs.sh" > "$tmp/failure.log" 2>&1; then
  echo 'failed documentation generation returned success' >&2
  exit 1
fi
[[ "$(cat "$fixture/docbuild/.lake/docs-source-rev")" == pre-failure-revision ]]
: > "$TEST_EVENTS"
printf 'pre-check-failure-revision\n' > "$fixture/docbuild/.lake/docs-source-rev"
if frun TEST_FAIL_DOC_LOCK_CHECK=1 "$fixture/scripts/build-docs.sh" > "$tmp/check-failure.log" 2>&1; then
  echo 'failed dependency verification returned success' >&2
  exit 1
fi
[[ "$(cat "$fixture/docbuild/.lake/docs-source-rev")" == pre-check-failure-revision ]]

# A stop present before invocation must preserve prior generated files and marker.
printf 'stop-before-revision\n' > "$fixture/docbuild/.lake/docs-source-rev"
mkdir -p "$fixture/docbuild/.lake/build/doc/TDA"
printf 'keep-me\n' > "$fixture/docbuild/.lake/build/doc/TDA/keep"
touch "$stop_file"
if frun CODEX_STOP_FILE="$stop_file" "$fixture/scripts/build-docs.sh" > "$tmp/stop-before.log" 2>&1; then
  echo 'pre-existing stop request was ignored' >&2
  exit 1
else
  status=$?
  [[ "$status" -eq 2 ]]
fi
[[ "$(cat "$fixture/docbuild/.lake/docs-source-rev")" == stop-before-revision ]]
[[ "$(cat "$fixture/docbuild/.lake/build/doc/TDA/keep")" == keep-me ]]
rm "$stop_file"
fi

# If stop is requested while waiting for the shared lock, recheck before invalidation.
printf 'stop-wait-revision\n' > "$fixture/docbuild/.lake/docs-source-rev"
printf 'keep-while-waiting\n' > "$fixture/docbuild/.lake/build/doc/TDA/keep"
ready="$tmp/lock-held"
(
  exec 9>>"$LOCK"
  flock -w 5 9 || exit 1
  touch "$ready"
  for _ in $(seq 1 1000); do
    [ -e "$release" ] && break
    sleep 0.01
  done
) & holder=$!
for _ in $(seq 1 500); do
  [ -e "$ready" ] && break
  kill -0 "$holder" 2>/dev/null || { echo 'test lock holder exited early' >&2; exit 1; }
  sleep 0.01
done
[ -e "$ready" ] || { echo 'test lock holder did not acquire shared lock' >&2; exit 1; }
if [ "${TEST_CLEANUP_FAIL_BEFORE_LOCK_ATTEMPT:-0}" = 1 ]; then
  touch "$stop_file"
fi
frun PATH="$tmp/bin:$PATH" WATCH_LOCK_ATTEMPTS="$tmp/lock-attempt" WATCH_LOCK_TARGET="$LOCK" \
  CODEX_STOP_FILE="$stop_file" timeout --kill-after=2s 10s \
  "$fixture/scripts/build-docs.sh" > "$tmp/stop-wait.log" 2>&1 & stopped=$!
if [ "${TEST_CLEANUP_FAIL_BEFORE_LOCK_ATTEMPT:-0}" = 1 ]; then
  exit 97
fi
for _ in $(seq 1 500); do
  [ -e "$tmp/lock-attempt" ] && break
  kill -0 "$stopped" 2>/dev/null || { cat "$tmp/stop-wait.log" >&2; exit 1; }
  sleep 0.01
done
[ -e "$tmp/lock-attempt" ] || { echo 'documentation build did not reach shared-lock wait' >&2; exit 1; }
if [ "${TEST_CLEANUP_FAIL_AFTER_LOCK_ATTEMPT:-0}" = 1 ]; then
  exit 97
fi
touch "$stop_file"
touch "$release"
wait "$holder"
if wait "$stopped"; then
  echo 'stop request during lock wait was ignored' >&2
  exit 1
else
  status=$?
  [[ "$status" -eq 2 ]]
fi
[[ "$(cat "$fixture/docbuild/.lake/docs-source-rev")" == stop-wait-revision ]]
[[ "$(cat "$fixture/docbuild/.lake/build/doc/TDA/keep")" == keep-while-waiting ]]

# Exercise the EXIT trap both before and during the builder's actual root-lock wait.
if [ "${TEST_CLEANUP_CHILD:-0}" != 1 ]; then
  for mode in TEST_CLEANUP_FAIL_BEFORE_LOCK_ATTEMPT TEST_CLEANUP_FAIL_AFTER_LOCK_ATTEMPT; do
    child_lock_report="$tmp/$mode.lock"
    set +e
    frun TEST_CLEANUP_CHILD=1 TEST_CLEANUP_LOCK_REPORT="$child_lock_report" "${mode}=1" \
      timeout 20s bash "$SOURCE_ROOT/scripts/agent/test-build-docs-lock.sh" \
      > "$tmp/$mode.log" 2>&1
    injected_status=$?
    set -e
    if [ "$injected_status" -ne 97 ]; then
      cat "$tmp/$mode.log" >&2
      echo "$mode returned $injected_status, expected 97" >&2
      exit 1
    fi
    IFS= read -r child_lock < "$child_lock_report"
    flock -w 5 -n "$child_lock" true || {
      echo "$mode leaked the shared build lock" >&2
      exit 1
    }
    echo "$mode cleanup OK (exit 97; shared lock released)"
  done
fi

echo 'build-docs transaction lock self-test OK (parallel, failure markers, stop, failure cleanup)'
