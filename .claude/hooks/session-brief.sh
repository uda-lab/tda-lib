#!/usr/bin/env bash
# SessionStart hook — wired by .claude/settings.json. Two jobs the recorded OOM incidents
# show must not depend on recall:
#   1. reap codex side-process chains of this repository's finished jobs whose worktree was
#      removed — ownership by launch tag and liveness per codex-chains.sh, never by path alone;
#   2. print the live resource state and the initialisation status, so every session opens
#      knowing its actual headroom and whether preflight has run.
# stdout is injected into the session as context.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="${CLAUDE_PROJECT_DIR:-$(cd "$HERE/../.." && pwd)}"
. "$HERE/codex-chains.sh"

libname="$(sed -n 's/^name = "\(.*\)"$/\1/p' "$ROOT/lakefile.toml" 2>/dev/null | head -1)"

# Owned (LOOP_JOB_ID=<libname>/…), no live process of that job, worktree removed. Chains with
# no tag in a removed worktree are only counted: their owner is unknown, so they are reported.
reaped=0; unowned=0
if [ -n "$libname" ] && [ -z "${LOOP_JOB_ID:-}" ]; then
  reaped="$(reap_codex_chains "${libname}/*" --deleted-cwd-only)" || reaped=0
fi
for pid in $(codex_chain_pids); do
  case "$(readlink "/proc/$pid/cwd" 2>/dev/null)" in
    *' (deleted)') [ -z "$(loop_job_of "$pid")" ] && unowned=$((unowned + 1)) ;;
  esac
done

avail_mib=$(( $(awk '/^MemAvailable:/{print $2}' /proc/meminfo 2>/dev/null || echo 0) / 1024 ))
cg_max="$(cat /sys/fs/cgroup/memory.max 2>/dev/null || echo max)"
if [ "$cg_max" = "max" ]; then cg_desc="no cgroup cap"; else cg_desc="$(awk -v b="$cg_max" 'BEGIN{printf "%.2f GiB cgroup cap", b / 1073741824}')"; fi
oom="$(awk '/^oom_kill /{print $2}' /sys/fs/cgroup/memory.events 2>/dev/null || echo '?')"
chains="$(codex_chain_pids | wc -l)"
oleans="$(find "$ROOT/.lake/packages/mathlib/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l)"

# `LeanScaffold` is the template sentinel: scripts/rename-project.sh leaves this file alone,
# so the comparison keeps working after the library is renamed.
if [ "$libname" = "LeanScaffold" ]; then
  init_state="NOT INITIALISED — this is a fresh scaffold. Do not start mathematical work; run the Init phase of .claude/skills/loop-orchestration-scaffold/SKILL.md first."
else
  # The container contract's directory is <project>-orchestration in the project's own
  # spelling (e.g. degree-labeling-orchestration for DegreeLabeling); find it, never derive it.
  # A vendored skill can end in -orchestration too, so prefer the candidate whose frontmatter
  # says "Container contract" (the template's wording) over the first glob match.
  contract=""
  for f in "$ROOT"/.claude/skills/*-orchestration/SKILL.md; do
    [ -f "$f" ] || continue
    if grep -q '^description: Container contract' "$f"; then contract="${f#"$ROOT"/}"; break; fi
    [ -n "$contract" ] || contract="${f#"$ROOT"/}"
  done
  if [ -n "$contract" ]; then
    init_state="initialised as ${libname}; the container contract is ${contract}."
  else
    init_state="initialised as ${libname}; no container contract found under .claude/skills/*-orchestration/ (Init Phase 3 generates it)."
  fi
fi

cat <<EOF
$(basename "$ROOT") session brief (.claude/hooks/session-brief.sh):
- state: ${init_state}
- memory: ${avail_mib} MiB available (${cg_desc}); oom_kill counter = ${oom}
- codex side-process chains alive: ${chains}$( [ "$reaped" -gt 0 ] && printf ' (reaped %s of finished jobs whose worktree was removed)' "$reaped" )$( [ "$unowned" -gt 0 ] && printf '; %s untagged in removed worktrees, owner unknown, not stopped' "$unowned" )
- mathlib oleans present: ${oleans}. Near zero means \`scripts/bootstrap.sh\` has not run; never
  let \`lake build\` cold-compile mathlib in a small container (hours, and it will OOM).
- Every Lean invocation is gated by the PreToolUse hook .claude/hooks/lean-guard.sh: it must
  hold flock /tmp/lean-build.lock, carry no -M/-j, and start with >= ${LEAN_GUARD_MIN_AVAIL_MIB:-1536} MiB free.
EOF
