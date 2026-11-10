#!/usr/bin/env bash
# Re-run Git-sensitive fixture suites with an unrelated repository and hostile
# external Git configuration selected by the caller.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d /tmp/tda-git-fixture-isolation.XXXXXX)"
trap 'rm -rf -- "$tmp"' EXIT
foreign="$tmp/foreign"
mkdir -p "$foreign" "$tmp/global-hooks"

fenv() {
  env -u GIT_DIR -u GIT_WORK_TREE -u GIT_INDEX_FILE \
    GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 "$@"
}
fgit() { fenv git "$@"; }

fgit -C "$foreign" init -q
fgit -C "$foreign" config user.name 'Isolation Fixture'
fgit -C "$foreign" config user.email 'isolation@example.invalid'
printf 'foreign fixture\n' > "$foreign/tracked.txt"
fgit -C "$foreign" add tracked.txt
fgit -C "$foreign" commit -qm 'foreign fixture baseline'

cat > "$tmp/global-hooks/pre-commit" <<EOF
#!/usr/bin/env sh
printf 'global hook ran\\n' >> '$tmp/global-hook-ran'
exit 0
EOF
chmod +x "$tmp/global-hooks/pre-commit"
cat > "$tmp/global.gitconfig" <<EOF
[user]
  signingkey = issue-713-no-such-signing-key
[commit]
  gpgsign = true
[core]
  hooksPath = $tmp/global-hooks
EOF
cat > "$tmp/system.gitconfig" <<EOF
[init]
  defaultBranch = system-poisoned
EOF

hostile_git() {
  env -u GIT_CONFIG_NOSYSTEM \
    GIT_CONFIG_GLOBAL="$tmp/global.gitconfig" \
    GIT_CONFIG_SYSTEM="$tmp/system.gitconfig" \
    git -C "$foreign" "$@"
}
[[ "$(hostile_git config --get commit.gpgsign)" == true ]]
[[ "$(hostile_git config --get core.hooksPath)" == "$tmp/global-hooks" ]]
[[ "$(hostile_git config --get init.defaultBranch)" == system-poisoned ]]

snapshot() {
  python3 - "$1" "$2" <<'PY'
import hashlib, json, os, pathlib, stat, subprocess, sys

root = pathlib.Path(sys.argv[1]).resolve()
destination = pathlib.Path(sys.argv[2])
env = os.environ.copy()
for key in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE"):
    env.pop(key, None)
env["GIT_CONFIG_GLOBAL"] = "/dev/null"
env["GIT_CONFIG_NOSYSTEM"] = "1"
# `git status` may refresh stale index stat data even on a clean worktree. This
# snapshot must observe repository state without writing optional index locks.
env["GIT_OPTIONAL_LOCKS"] = "0"

def git(*args):
    return subprocess.check_output(["git", "-C", str(root), *args], env=env)

git_dir = pathlib.Path(os.fsdecode(git("rev-parse", "--absolute-git-dir").strip()))
index = pathlib.Path(os.fsdecode(git("rev-parse", "--git-path", "index").strip()))
if not index.is_absolute():
    index = root / index
index_digest = hashlib.sha256(index.read_bytes()).hexdigest() if index.exists() else None
refs = git("for-each-ref", "--format=%(refname) %(objectname)").decode()
try:
    head_ref = git("symbolic-ref", "-q", "HEAD").decode().strip()
except subprocess.CalledProcessError:
    head_ref = None
try:
    head = git("rev-parse", "--verify", "HEAD").decode().strip()
except subprocess.CalledProcessError:
    head = None
status = git("status", "--porcelain=v1", "-z", "--untracked-files=no").hex()
tracked = git("ls-files", "-z").split(b"\0")
worktree = hashlib.sha256()
for raw_path in tracked:
    if not raw_path:
        continue
    path = root / os.fsdecode(raw_path)
    entry = hashlib.sha256()
    try:
        info = path.lstat()
    except FileNotFoundError:
        worktree.update(raw_path + b"\0MISSING\0")
        continue
    entry.update(str(stat.S_IFMT(info.st_mode)).encode() + b":" + oct(stat.S_IMODE(info.st_mode)).encode() + b"\0")
    if stat.S_ISLNK(info.st_mode):
        entry.update(os.fsencode(os.readlink(path)))
    elif stat.S_ISREG(info.st_mode):
        with path.open("rb") as stream:
            while chunk := stream.read(1024 * 1024):
                entry.update(chunk)
    elif stat.S_ISDIR(info.st_mode):
        try:
            subhead = subprocess.check_output(["git", "-C", str(path), "rev-parse", "--verify", "HEAD"], env=env)
        except (subprocess.CalledProcessError, NotADirectoryError):
            subhead = b"NO_SUBMODULE_HEAD"
        entry.update(subhead)
    worktree.update(raw_path + b"\0" + entry.digest())
record = {
    "git_dir": str(git_dir),
    "index_sha256": index_digest,
    "refs": refs,
    "head_ref": head_ref,
    "head": head,
    "tracked_status_hex": status,
    "tracked_worktree_sha256": worktree.hexdigest(),
}
destination.write_text(json.dumps(record, sort_keys=True, indent=2) + "\n")
PY
}

# A newer mtime with unchanged contents makes Git's cached stat data stale. Taking
# the snapshot must not itself refresh and rewrite the repository index.
stale_probe="$tmp/stale-index-probe"
mkdir -p "$stale_probe"
fgit -C "$stale_probe" init -q
fgit -C "$stale_probe" config user.name 'Snapshot Fixture'
fgit -C "$stale_probe" config user.email 'snapshot@example.invalid'
printf 'unchanged tracked content\n' > "$stale_probe/tracked.txt"
fgit -C "$stale_probe" add tracked.txt
fgit -C "$stale_probe" commit -qm 'stale index baseline'
sleep 1
touch "$stale_probe/tracked.txt"
stale_index="$stale_probe/.git/index"
stale_index_before="$(sha256sum "$stale_index" | cut -d' ' -f1)"
snapshot "$stale_probe" "$tmp/stale-index.snapshot.json"
stale_index_after="$(sha256sum "$stale_index" | cut -d' ' -f1)"
stale_snapshot_index="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["index_sha256"])' "$tmp/stale-index.snapshot.json")"
stale_status="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["tracked_status_hex"])' "$tmp/stale-index.snapshot.json")"
if [ "$stale_index_before" != "$stale_index_after" ] || [ "$stale_index_before" != "$stale_snapshot_index" ] || [ -n "$stale_status" ]; then
  echo 'FAIL snapshot changed a stale index or marked clean content as modified' >&2
  exit 1
fi
echo 'PASS stale-index snapshot leaves repository index unchanged'

snapshot "$foreign" "$tmp/foreign.before.json"
snapshot "$ROOT" "$tmp/checkout.before.json"

run_suite() {
  local label="$1"; shift
  local status
  printf 'Running %s under foreign GIT_DIR and hostile global/system config...\n' "$label"
  if env \
    -u GIT_CONFIG_NOSYSTEM \
    GIT_DIR="$foreign/.git" \
    GIT_WORK_TREE="$foreign" \
    GIT_INDEX_FILE="$foreign/.git/index" \
    GIT_CONFIG_GLOBAL="$tmp/global.gitconfig" \
    GIT_CONFIG_SYSTEM="$tmp/system.gitconfig" \
    TDA_GIT_FIXTURE_ISOLATION_CHILD=1 \
    "$@"; then
    printf 'PASS %s\n' "$label"
  else
    status=$?
    printf 'FAIL %s (exit %s)\n' "$label" "$status" >&2
    return "$status"
  fi
}

failed=0
run_suite 'scripts/test-guards.sh' bash "$ROOT/scripts/test-guards.sh" || failed=1
run_suite 'scripts/agent/test-layout.sh' bash "$ROOT/scripts/agent/test-layout.sh" || failed=1
run_suite 'scripts/agent/test-build-docs-lock.sh' bash "$ROOT/scripts/agent/test-build-docs-lock.sh" || failed=1

snapshot "$foreign" "$tmp/foreign.after.json"
snapshot "$ROOT" "$tmp/checkout.after.json"
for repo in foreign checkout; do
  if ! cmp -s "$tmp/$repo.before.json" "$tmp/$repo.after.json"; then
    printf 'FAIL %s repository state changed under the test suites:\n' "$repo" >&2
    diff -u "$tmp/$repo.before.json" "$tmp/$repo.after.json" >&2 || true
    failed=1
  else
    printf 'PASS %s repository index, refs, and tracked worktree unchanged\n' "$repo"
  fi
done
if [ -e "$tmp/global-hook-ran" ]; then
  echo 'FAIL hostile global Git hook ran' >&2
  failed=1
else
  echo 'PASS hostile global signing and hooks did not affect fixtures'
fi

if [ "$failed" -ne 0 ]; then
  exit 1
fi
echo 'Git fixture isolation regression OK'
