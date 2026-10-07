#!/usr/bin/env bash
# Self-test for lean-guard.sh: feeds PreToolUse JSON and checks allow (0) / block (2).
# Run after every edit of the guard:  bash .claude/hooks/test-lean-guard.sh
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GUARD="$HERE/lean-guard.sh"
fail=0; n=0

# Memory-headroom rule is environment-dependent; disable it for the deterministic cases.
export LEAN_GUARD_MIN_AVAIL_MIB=0
HOME="$(mktemp -d)"; export HOME   # no ~/.codex snapshot → overage rule inert
rm -f /tmp/codex-stop.test-guard

check() {  # check <expected-exit> <command-text>
  local want="$1" cmd="$2" got
  n=$((n + 1))
  printf '{"tool_input":{"command":%s}}' "$(printf '%s' "$cmd" | jq -Rs .)" | bash "$GUARD" >/dev/null 2>&1
  got=$?
  if [ "$got" -ne "$want" ]; then
    echo "FAIL [$n] want $want got $got: $cmd"; fail=1
  fi
}

# allow
check 0 'bash scripts/check.sh'
check 0 '( flock 9; lake build ) 9>/tmp/lean-build.lock'
check 0 'flock /tmp/lean-build.lock lake env lean scripts/print_axioms.lean'
check 0 'LEAN_NUM_THREADS=2 flock /tmp/lean-build.lock lake build'
check 0 'git status && ls'
check 0 'cat <<EOF
lake build is mentioned in prose only
EOF'
check 0 'bash scripts/hooks/pre-push'
check 0 'grep -rn "lake build" docs/'
check 0 'bash scripts/check.sh | tail -3; git commit -m "guard: require flock on lake build"'
check 0 'gh api -X POST repos/o/r/pulls/2/comments/1/replies -f body="use ( flock 9; lake build ) 9>/tmp/lean-build.lock"'
check 0 "git commit -m 'never run lean file.lean bare'"
check 2 'bash -c "lake build"'
check 2 "sh -c 'lean X.lean'"
check 0 'flock /tmp/lean-build.lock sh -c "lake build"'
check 2 'flock -w 10 /tmp/lean-build.lock bash scripts/hooks/pre-push'
check 0 'flock -w 60 /tmp/lean-build.lock lake build'
check 0 '( flock 9; lake build; lake env lean scripts/print_axioms.lean ) 9>/tmp/lean-build.lock'
check 0 'flock /tmp/lean-build.lock bash -c "lake build && lake env lean x.lean"'
# block: wrong lock, unrelated flock, fd form without the redirect
check 2 'flock /tmp/wrong.lock lake build'
check 2 'echo flock; lake build'
check 2 'flock /tmp/lean-build.lock true; lake build'
check 2 '( flock 9; lake build )'
check 2 '( flock 8; lake build ) 9>/tmp/lean-build.lock'
check 2 'lake build'
# fd form scoped to its command group
check 2 '( flock 9; true ) 9>/tmp/lean-build.lock; lake build'
check 2 '( flock 9; true ) 9>/tmp/lean-build.lock && lake build'
check 0 '( flock 9; ( lake build ) ) 9>/tmp/lean-build.lock'
check 0 'exec 9>/tmp/lean-build.lock; flock 9; lake build'
check 0 '( flock 9 && lake build && lake env lean x.lean ) 9>/tmp/lean-build.lock'

# redirects bind to the command that owns them; substitutions execute even inside quotes
check 2 'true 9>/tmp/lean-build.lock; flock 9; lake build'
check 2 'echo "$(lake build)"'
check 2 'x=`lake build`'
check 2 'echo "started" && echo "$(flock 9; lake build)"'
check 0 'echo "$(flock /tmp/lean-build.lock lake build)"'
check 0 '( flock 9; echo "$(lake build)" ) 9>/tmp/lean-build.lock'
check 2 'diff <(lake env lean a.lean) <(cat b)'
check 2 'flock /tmp/lean-build.lock true; bash -c "lake build"'
check 0 "flock /tmp/lean-build.lock bash -c 'lake build; lake env lean x.lean'"
check 0 'flock /tmp/lean-build.lock bash -c "echo \"go\"; lake build"'
check 2 'flock /tmp/lean-build.lock bash -c "bash scripts/check.sh"'

# heredocs are data unless a shell interpreter executes them
check 2 $'bash <<EOF\nlake build\nEOF'
check 2 $'sh -s <<\'EOF\'\nlake env lean x.lean\nEOF'
check 0 $'cat <<EOF\nlake build\nEOF'
check 0 $'gh pr comment 2 --body-file - <<EOF\nrun lake build under flock\nEOF'
check 0 $'bash <<EOF\nflock /tmp/lean-build.lock lake build\nEOF'
# quoted or path-qualified executables
check 2 '"lake" build'
check 2 "'lake' build"
check 2 '$HOME/.elan/bin/lake build'
check 2 '/workspaces/.elan/bin/lean X.lean'
check 0 'flock /tmp/lean-build.lock "$HOME/.elan/bin/lake" build'
check 0 'echo "lake build is what CI does"'
# eval executes its argument
check 2 'eval "lake build"'
check 2 "eval 'lake env lean x.lean'"
check 2 'eval lake build'
check 0 'eval "flock /tmp/lean-build.lock lake build"'
check 0 'flock /tmp/lean-build.lock bash -c "eval lake build"'
# syntax checks and linters of the gate scripts are not runs
export LEAN_GUARD_MIN_AVAIL_MIB=99999999
check 0 'bash -n scripts/check.sh && shellcheck scripts/check.sh scripts/hooks/pre-push'
check 0 'sed -n 1,20p scripts/check.sh'
check 2 './scripts/check.sh'
check 2 'bash -x scripts/hooks/pre-push'
export LEAN_GUARD_MIN_AVAIL_MIB=0
# a spoofed environment marker no longer exists; the gate is still a Lean invocation
check 0 'LEAN_SCAFFOLD_LOCKED=1 bash scripts/check.sh'
# fd-form outer lock around a self-locking script deadlocks
check 2 '( flock 9; bash scripts/check.sh ) 9>/tmp/lean-build.lock'
check 2 'exec 9>/tmp/lean-build.lock; flock 9; bash scripts/hooks/pre-push'

# headroom rule also covers the self-locking scripts
export LEAN_GUARD_MIN_AVAIL_MIB=99999999
check 2 'bash scripts/check.sh'
check 2 'bash scripts/hooks/pre-push'
check 2 'flock /tmp/lean-build.lock lake build'
check 0 'git status'
export LEAN_GUARD_MIN_AVAIL_MIB=0
check 2 'lean LeanScaffold/Basic.lean'
check 2 'lake env lean scripts/print_axioms.lean'
check 2 'LEAN_NUM_THREADS=2 timeout 600 nice lake build'
check 2 'flock /tmp/lean-build.lock lake build -j 4'
check 2 'flock /tmp/lean-build.lock lake build -M 4000'
check 2 'flock /tmp/lean-build.lock bash scripts/check.sh'
check 2 'cd sub && lake exe cache get'

# kill switch
touch /tmp/codex-stop.test-guard
# The guard reads /tmp/codex-stop; only test it when no real switch is engaged.
if [ ! -e /tmp/codex-stop ]; then
  echo test > /tmp/codex-stop
  check 2 'node "$CLAUDE_PLUGIN_ROOT/scripts/codex-companion.mjs" task --write "x"'
  check 2 'codex exec "x"'
  rm -f /tmp/codex-stop
  check 0 'codex exec "x"'
fi
rm -f /tmp/codex-stop.test-guard

if [ "$fail" -eq 0 ]; then echo "lean-guard self-test OK ($n cases)"; else exit 1; fi
