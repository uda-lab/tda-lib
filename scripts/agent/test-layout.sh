#!/usr/bin/env bash
# Exercise the real scanners in an isolated checkout-shaped fixture.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
fixture=$(mktemp -d)
trap 'rm -rf -- "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/TDA"
for name in check-no-sorry.sh check-no-custom-axiom.sh check-transient-artifacts.sh lean-code-scan.awk; do
  cp "$ROOT/scripts/$name" "$fixture/scripts/$name"
done
for harness in .agents .claude; do
  for area in scratch worktrees; do
    mkdir -p "$fixture/$harness/$area"
    printf 'theorem unfinished : True := by sorry\naxiom unchecked : False\n' > "$fixture/$harness/$area/Test.lean"
  done
done
printf 'theorem complete : True := by trivial\n' > "$fixture/TDA/Basic.lean"
for scanner in check-no-sorry.sh check-no-custom-axiom.sh; do
  bash "$fixture/scripts/$scanner" >/dev/null
  bash "$fixture/scripts/$scanner" --stable >/dev/null
done
printf 'theorem unfinished : True := by sorry\naxiom unchecked : False\n' > "$fixture/TDA/Basic.lean"
for scanner in check-no-sorry.sh check-no-custom-axiom.sh; do
  if bash "$fixture/scripts/$scanner" >/dev/null 2>&1; then echo "FAIL: $scanner ignored library violation"; exit 1; fi
  if bash "$fixture/scripts/$scanner" --stable >/dev/null 2>&1; then echo "FAIL: stable $scanner ignored library violation"; exit 1; fi
done
# Marked development debt passes normal mode but never stable mode.
printf 'theorem unfinished : True := by sorry -- ALLOW_SORRY: #3 fixture\naxiom unchecked : False -- ALLOW_AXIOM: #3 fixture\n' > "$fixture/TDA/Basic.lean"
for scanner in check-no-sorry.sh check-no-custom-axiom.sh; do
  bash "$fixture/scripts/$scanner" >/dev/null
  if bash "$fixture/scripts/$scanner" --stable >/dev/null 2>&1; then echo "FAIL: stable $scanner accepted marked debt"; exit 1; fi
done
git -C "$fixture" init -q
git -C "$fixture" add .agents/worktrees/Test.lean
if bash "$fixture/scripts/check-transient-artifacts.sh" >/dev/null 2>&1; then echo 'FAIL: tracked .agents worktree accepted'; exit 1; fi
# The actual checkout's shared skill topology must stay canonical.
for skill in "$ROOT"/.agents/skills/*; do
  [ -d "$skill" ] && [ ! -L "$skill" ]
  legacy="$ROOT/.claude/skills/$(basename "$skill")"
  [ -L "$legacy" ] && [ -f "$legacy/SKILL.md" ]
  [ "$(cd "$skill" && pwd -P)" = "$(cd "$legacy" && pwd -P)" ]
done
# Native Codex hook commands resolve from arbitrary project subdirectories.
python3 - "$ROOT" <<'PY'
import json, pathlib, subprocess, sys
root = pathlib.Path(sys.argv[1])
hooks = json.loads((root / '.codex/hooks.json').read_text())['hooks']
for event in ('SessionStart', 'PreToolUse'):
    command = hooks[event][0]['hooks'][0]['command']
    result = subprocess.run(command, shell=True, cwd=root / 'scripts', input='{"tool_input":{"command":"git status"}}', text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert result.returncode == 0, (event, result.stderr)
PY
echo 'layout/scanner migration self-tests OK'
