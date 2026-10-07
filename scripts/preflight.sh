#!/usr/bin/env bash
# Preflight report: the measured facts an orchestrator needs before its first dispatch.
# Read-only — performs no build, no fetch, no GitHub mutation. Exit 0 whenever the report
# could be produced; the findings (not the exit code) decide what to do next. Each line is
# `key: value` so a harness can grep it; write the summary into the container contract
# (.claude/skills/<project>-orchestration/SKILL.md), not into a tracked status file.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1
export PATH="$HOME/.elan/bin:${ELAN_HOME:-/nonexistent}/bin:$PATH"

say() { printf '%s: %s\n' "$1" "$2"; }
have() { command -v "$1" >/dev/null 2>&1; }

echo "== repository"
say "root" "$ROOT"
say "library" "$(sed -n 's/^name = "\(.*\)"$/\1/p' lakefile.toml | head -1)"
# `LeanScaffold` is the template sentinel; scripts/rename-project.sh leaves this file alone.
say "initialised" "$( [ "$(sed -n 's/^name = "\(.*\)"$/\1/p' lakefile.toml | head -1)" = LeanScaffold ] && echo no || echo yes )"
say "toolchain" "$(cat lean-toolchain 2>/dev/null || echo missing)"
say "mathlib_pin" "$(sed -n 's/^rev = "\(.*\)"$/\1/p' lakefile.toml | head -1)"
say "remote" "$(git remote get-url origin 2>/dev/null || echo none)"
say "default_branch" "$(git symbolic-ref --short refs/remotes/origin/HEAD 2>/dev/null | sed 's#origin/##' || gh repo view --json defaultBranchRef --jq .defaultBranchRef.name 2>/dev/null || echo unknown)"
say "hooks_path" "$(git config core.hooksPath 2>/dev/null || echo unset)"

echo "== machine"
say "cpus" "$(nproc 2>/dev/null || echo '?')"
say "mem_available_mib" "$(( $(awk '/^MemAvailable:/{print $2}' /proc/meminfo 2>/dev/null || echo 0) / 1024 ))"
cg="$(cat /sys/fs/cgroup/memory.max 2>/dev/null || echo max)"
say "cgroup_mem_max" "$( [ "$cg" = max ] && echo none || awk -v b="$cg" 'BEGIN{printf "%.2f GiB", b/1073741824}')"
say "cgroup_swap_max" "$(cat /sys/fs/cgroup/memory.swap.max 2>/dev/null || echo unknown)"
say "oom_kill_count" "$(awk '/^oom_kill /{print $2}' /sys/fs/cgroup/memory.events 2>/dev/null || echo '?')"
say "disk_free" "$(df -h . 2>/dev/null | awk 'NR==2{print $4}')"
say "build_lock" "/tmp/lean-build.lock$( [ -e /tmp/lean-build.lock ] && echo ' (exists)' )"

echo "== lean"
say "elan" "$(have elan && elan --version 2>/dev/null | head -1 || echo missing)"
say "lake" "$(have lake && echo present || echo missing)"
say "mathlib_oleans" "$(find .lake/packages/mathlib/.lake/build/lib -name '*.olean' 2>/dev/null | wc -l)"
say "mathlib_cache_dir" "${MATHLIB_CACHE_DIR:-unset}"
say "lean_num_threads" "${LEAN_NUM_THREADS:-unset}"
# Other checkouts on this machine with the same pin can share their package oleans by
# hardlink (`cp -al <that>/.lake/packages .lake/packages`); never hardlink .lake/build.
pin="$(cat lean-toolchain 2>/dev/null)"
for d in "$ROOT"/../*/ "$ROOT"/../../*/; do
  [ -f "$d/lean-toolchain" ] && [ "$(cat "$d/lean-toolchain")" = "$pin" ] && [ "$(cd "$d" && pwd)" != "$ROOT" ] \
    && [ -d "$d/.lake/packages/mathlib" ] && say "sharable_packages" "$(cd "$d" && pwd)/.lake/packages"
done 2>/dev/null

echo "== github"
if have gh; then
  say "gh_user" "$(gh api user --jq .login 2>/dev/null || echo unauthenticated)"
  repo="$(gh repo view --json nameWithOwner --jq .nameWithOwner 2>/dev/null || true)"
  say "gh_repo" "${repo:-unknown}"
  if [ -n "$repo" ]; then
    say "gh_permissions" "$(gh api "repos/$repo" --jq '.permissions | to_entries | map(select(.value)) | map(.key) | join(",")' 2>/dev/null || echo '?')"
    say "rulesets" "$(gh api "repos/$repo/rulesets" --jq 'map(.name) | join(",")' 2>/dev/null || echo none)"
    say "labels_hard_stop" "$(gh label list --repo "$repo" --json name --jq '[.[].name] | map(select(. == "blocked" or . == "needs-decision" or . == "do-not-merge" or . == "agent:ready")) | join(",")' 2>/dev/null)"
    say "charter_issue" "$(gh api graphql -f query='{repository(owner:"'"${repo%%/*}"'",name:"'"${repo##*/}"'"){pinnedIssues(first:1){nodes{issue{number}}}}}' --jq '.data.repository.pinnedIssues.nodes[0].issue.number' 2>/dev/null || echo none)"
  fi
else
  say "gh" "missing"
fi

echo "== review"
say "REVIEW_ACQUIRE_SCRIPT" "${REVIEW_ACQUIRE_SCRIPT:-unset (bundled github-driven-workflow acquire-review.py or a Reviewed-by artifact route applies)}"
[ -n "${REVIEW_ACQUIRE_SCRIPT:-}" ] && say "review_script_executable" "$( [ -x "$REVIEW_ACQUIRE_SCRIPT" ] && echo yes || echo no )"

echo "== harnesses"
say "claude" "$(have claude && claude --version 2>/dev/null | head -1 || echo missing)"
say "codex" "$(have codex && codex --version 2>/dev/null | head -1 || echo missing)"
say "codex_plugin_root" "${CLAUDE_PLUGIN_ROOT:-$(ls -d "$HOME"/.claude/plugins/cache/openai-codex/codex/* 2>/dev/null | tail -1)}"
say "copilot" "$(have copilot && echo present || echo missing)"
say "auggie" "$(have auggie && echo present || echo missing)"
# Claude Code discovers skills under .claude/skills and ~/.claude/skills; Codex under
# .agents/skills and ~/.agents/skills. The bundled skills are tracked under both (the
# .agents entries are relative symlinks); prerequisites are reported per vendor.
say "skills_user_claude" "$(ls "$HOME/.claude/skills" 2>/dev/null | tr '\n' ' ')"
say "skills_user_codex" "$(ls "$HOME/.agents/skills" 2>/dev/null | tr '\n' ' ')"
say "skills_repo_claude" "$(ls .claude/skills 2>/dev/null | tr '\n' ' ')"
say "skills_repo_codex" "$(ls .agents/skills 2>/dev/null | tr '\n' ' ')"
for s in github-driven-workflow github-loop-engineering lean-formalization-discipline; do
  if [ -f "$HOME/.claude/skills/$s/SKILL.md" ] || [ -f ".claude/skills/$s/SKILL.md" ]; then say "skill_${s}_claude" present; else say "skill_${s}_claude" "MISSING (see docs/orchestration.md § Prerequisites)"; fi
  if [ -f "$HOME/.agents/skills/$s/SKILL.md" ] || [ -f ".agents/skills/$s/SKILL.md" ]; then say "skill_${s}_codex" present; else say "skill_${s}_codex" "MISSING (see docs/orchestration.md § Prerequisites)"; fi
done
codex_home="${CODEX_HOME:-$HOME/.codex}"
if [ -f "$codex_home/config.toml" ]; then say "codex_default_model" "$(sed -n 's/^model *= *"\(.*\)"/\1/p' "$codex_home/config.toml" | head -1)"; fi
# Codex rate-limit snapshot: the newest `token_count` event carrying `rate_limits` across the
# most recent rollout files (the newest file alone can be a stalled session whose last line
# predates a window reset). Reported with its sample time and the reset time; `stale` means
# the reset has passed, so the number describes the previous window and says nothing about
# the live one until the next Codex request. The same event carries the prepaid-credit
# balance: at 100 % of the window the CLI keeps going on credits, so a non-zero balance is
# pay-as-you-go exposure for a run that must stop at 100 % (a check before each request
# narrows the exposure; only a zero balance removes it).
best_ts=""; best_line=""
while IFS= read -r f; do
  [ -f "$f" ] || continue
  # Only events whose `primary` is an object: `premium` rate-limit events carry null windows.
  line="$(grep '"rate_limits":{[^{]*"primary":{' "$f" 2>/dev/null | tail -1)"
  [ -n "$line" ] || continue
  ts="$(printf '%s' "$line" | sed -n 's/^{"timestamp":"\([^"]*\)".*/\1/p')"
  if [ -n "$ts" ] && [ "$ts" \> "$best_ts" ]; then best_ts="$ts"; best_line="$line"; fi
done < <(ls -t "$codex_home"/sessions/*/*/*/*.jsonl 2>/dev/null | head -16)
if [ -n "$best_line" ]; then
  rl="$(printf '%s' "$best_line" | grep -o '"rate_limits":{.*' | head -c 2000)"
  rl_field() { printf '%s' "$rl" | grep -o "\"$1\":{[^}]*}" | head -1 | sed -n "s/.*\"$2\":\([^,}]*\).*/\1/p" | tr -d '"'; }
  rl_time() { [ -n "$1" ] && date -u -d "@$1" +%Y-%m-%dT%H:%M:%SZ 2>/dev/null || echo unknown; }
  used="$(rl_field primary used_percent)"; win="$(rl_field primary window_minutes)"; resets="$(rl_field primary resets_at)"
  sec_used="$(rl_field secondary used_percent)"; sec_resets="$(rl_field secondary resets_at)"
  credits="$(rl_field credits balance)"
  stale=no; [ -n "$resets" ] && [ "$resets" -lt "$(date -u +%s)" ] 2>/dev/null && stale=yes
  say "codex_window" "primary used_percent=${used:-?} window_minutes=${win:-?} resets_at=$(rl_time "$resets"); secondary used_percent=${sec_used:-?} resets_at=$(rl_time "$sec_resets")"
  say "codex_window_sampled_at" "$best_ts"
  say "codex_window_stale" "$stale$( [ "$stale" = yes ] && echo ' (reset time has passed; the live window is unknown until the next Codex request)')"
  say "codex_credits" "balance=${credits:-unknown} (the CLI spills onto prepaid credits at 100 % of the window; non-zero = pay-as-you-go exposure)"
else
  say "codex_window" "unknown (no rollout with rate_limits under $codex_home/sessions)"
fi
say "codex_stop_switch" "$( [ -e /tmp/codex-stop ] && echo "ON ($(cat /tmp/codex-stop))" || echo off )"

echo "PREFLIGHT OK — next: scripts/bootstrap.sh (if mathlib_oleans is near 0), then scripts/check.sh"
