#!/usr/bin/env bash
# PreToolUse(Bash) guard — makes the memory-unsafe Lean invocations unreachable instead of
# relying on an agent remembering a rule. Wired by .claude/settings.json.
#
# Every OOM incident recorded on the source projects came from one of four shapes:
#   1. a Lean invocation outside `flock /tmp/lean-build.lock` (two builds at once);
#   2. a standalone `lean file.lean` / `lake env lean` type-check bypassing the lock;
#   3. hand-rolled `-M` / `-j` limits (Lake 5 has no `-j`; `-M` overrides the safe default);
#   4. starting any build while free headroom is already gone (unreaped side processes).
# It also refuses to wrap a self-locking repository script in an outer flock (deadlock),
# and it enforces the codex kill switch (/tmp/codex-stop) and the codex overage guard.
#
# The command text is parsed by .claude/hooks/lean-cmd-parse.awk (quotes, substitutions,
# subshells, `sh -c` arguments, redirect binding); heredoc bodies are removed first.
#
# Tunables (env, e.g. via .claude/settings.local.json):
#   LEAN_GUARD_MIN_AVAIL_MIB   headroom required before a build starts (default 1536)
#   LEAN_GUARD_DISABLE=1       turn the guard off (large machines with no shared cgroup)
#
# Contract: exit 0 = allow, exit 2 = block with the stderr text shown to the model.
set -uo pipefail

[ "${LEAN_GUARD_DISABLE:-0}" = "1" ] && exit 0

MIN_AVAIL_KB=$(( ${LEAN_GUARD_MIN_AVAIL_MIB:-1536} * 1024 ))
LOCK=/tmp/lean-build.lock

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$HERE/codex-chains.sh"

input="$(cat)"
cmd="$(printf '%s' "$input" | jq -r '.tool_input.command // ""' 2>/dev/null)"
[ -z "$cmd" ] && exit 0

deny() {
  printf 'LEAN GUARD (.claude/hooks/lean-guard.sh) — command blocked.\n\n%s\n' "$1" >&2
  exit 2
}

# Heredoc bodies are data, not commands: a dispatch prompt or a doc that merely mentions
# `lake build` must not trip the guard. Strip them before any matching — unless the heredoc
# feeds a shell interpreter (`bash <<EOF`, `sh -s <<'EOF'`), in which case the body IS a
# shell program and is kept for the parser (each body line is a command line).
stripped="$(printf '%s\n' "$cmd" | awk '
  BEGIN { inhd = 0; delim = ""; keep = 0 }
  {
    if (inhd) {
      if ($0 ~ "^[[:space:]]*" delim "[[:space:]]*$") { inhd = 0; next }
      if (keep) print
      next
    }
    if (match($0, /<<-?[[:space:]]*"?'"'"'?[A-Za-z_][A-Za-z0-9_]*"?'"'"'?/)) {
      d = substr($0, RSTART, RLENGTH); before = substr($0, 1, RSTART - 1)
      sub(/<<-?[[:space:]]*/, "", d); gsub(/["'"'"']/, "", d)
      delim = d; inhd = 1
      keep = (before ~ /(^|[[:space:];&|(])(ba|z|da)?sh([[:space:]]+-[A-Za-z]+)*[[:space:]]*$/) ? 1 : 0
    }
    print
  }')"

# --- rule 0: codex kill switch and overage guard --------------------------------------
# codex jobs bill pay-as-you-go credits once the 5-hour window is at 100 %. A driver
# mid-turn cannot be reached by message, so the stop must be mechanical:
#   * /tmp/codex-stop present  → every codex invocation is blocked (the orchestrator's switch);
#   * newest ~/.codex/sessions snapshot shows used_percent >= 100 with resets_at in the
#     future → blocked (no overage spend, ever).
# Matched on the raw text (the plugin path is normally quoted); erring towards blocking is
# the right side for a spend guard.
if printf '%s' "$stripped" | grep -qE 'codex-companion\.mjs|(^|[[:space:];&|(])codex[[:space:]]+(exec|app-server|task|review)'; then
  if [ -e /tmp/codex-stop ]; then
    deny "codex is switched OFF by the orchestrator (/tmp/codex-stop exists: $(cat /tmp/codex-stop 2>/dev/null)).
Do not retry; use the Claude-subagent worker/review routes. Read the latest orchestrator
comment on your Issue for the current ruling."
  fi
  newest="$(ls -t "$HOME"/.codex/sessions/*/*/*/*.jsonl 2>/dev/null | head -1)"
  if [ -n "$newest" ]; then
    snap="$(grep -o '"primary":{[^}]*}' "$newest" 2>/dev/null | tail -1)"
    used="$(printf '%s' "$snap" | grep -o '"used_percent":[0-9.]*' | grep -o '[0-9.]*$')"
    resets="$(printf '%s' "$snap" | grep -o '"resets_at":[0-9]*' | grep -o '[0-9]*$')"
    if [ -n "$used" ] && [ -n "$resets" ] && [ "$resets" -gt "$(date +%s)" ] \
       && [ "$(printf '%s' "$used" | cut -d. -f1)" -ge 100 ]; then
      deny "codex window is at ${used}% (resets $(date -u -d @"$resets" +%H:%MZ)); a job now would bill
pay-as-you-go credits, which is a financial commitment the loop never makes.
Use the Claude-subagent routes until the window resets."
    fi
  fi
fi

# --- parse: Lean segments with lock status, self-locking scripts ------------------------
findings="$(printf '%s' "$stripped" | awk -v LOCK="$LOCK" -f "$HERE/lean-cmd-parse.awk")"
[ -z "$findings" ] && exit 0

# --- rule: never wrap a self-locking repository script in an outer flock ---------------
if printf '%s\n' "$findings" | grep -qx 'SELFLOCK 1'; then
  deny "scripts/check.sh and scripts/hooks/pre-push take \`flock $LOCK\` themselves.
Wrapping them in another flock self-deadlocks: the parent holds the lock and the child
waits for it forever. Run the script bare."
fi

lean_texts="$(printf '%s\n' "$findings" | sed -n 's/^LEAN [01] //p')"

# --- rule 3: no hand-rolled memory/parallelism limits ---------------------------------
if printf '%s\n' "$lean_texts" | grep -qE '(^|[[:space:]])-M[[:space:]]*[0-9]'; then
  deny "\`-M\` sets Lean's own memory ceiling and has repeatedly been set high enough to
OOM a shared container. Drop it. Control parallelism with LEAN_NUM_THREADS instead
(set it in .claude/settings.local.json for this machine)."
fi
if printf '%s\n' "$lean_texts" | grep -qE '(^|[[:space:]])-j[[:space:]]*[0-9]'; then
  deny "Lake 5.x has no \`-j\` flag — it fails with \"unknown short option '-j'\" and the
build never runs. Parallelism is Lean's internal scheduler; control it with
LEAN_NUM_THREADS, not with a lake CLI flag."
fi

# --- rules 1 & 2: every Lean invocation must hold the build lock -----------------------
if printf '%s\n' "$findings" | grep -q '^LEAN 0 '; then
  deny "Every Lean invocation must be serialised on $LOCK — that includes standalone
\`lean file.lean\` and \`lake env lean\` type-checks, not just \`lake build\`, and a build
started from a command substitution or a subshell. Two concurrent Lean process groups do
not fit in a small shared container.

Use one of:
  bash scripts/check.sh                     # canonical gate; takes the lock itself
  ( flock 9; lake build ) 9>$LOCK           # raw build
  flock $LOCK lake env lean <file>.lean"
fi

# --- rule 4: refuse to start without headroom -----------------------------------------
# Applies to raw Lean invocations and to the self-locking gate scripts alike.
# Headroom = min(host MemAvailable, cgroup allowance). Inside a cgroup-limited container
# /proc/meminfo reports the host/VM, which can show gigabytes free while this cgroup is a
# few MB from its own memory.max; the cgroup figure is what the OOM killer acts on.
# The cgroup allowance is memory.max − non-reclaimable usage, where non-reclaimable =
# memory.current − (file − shmem). memory.current includes the page cache, and a container
# that has mmapped a multi-GB olean tree sits within a few hundred MiB of its cap permanently
# while those file pages are exactly what the kernel reclaims first; anon/shmem/kernel memory
# is what actually competes with a new Lean process. (Counting only inactive_file, as
# `docker stats` does, blocked every build on the reference container: 877 MiB "available"
# with 1.4 GiB of clean olean cache resident.)
avail="$(awk '/^MemAvailable:/{print $2}' /proc/meminfo 2>/dev/null)"
cg_max="$(cat /sys/fs/cgroup/memory.max 2>/dev/null || echo max)"
cg_cur="$(cat /sys/fs/cgroup/memory.current 2>/dev/null || echo 0)"
cg_file="$(awk '/^file /{print $2}' /sys/fs/cgroup/memory.stat 2>/dev/null || echo 0)"
cg_shmem="$(awk '/^shmem /{print $2}' /sys/fs/cgroup/memory.stat 2>/dev/null || echo 0)"
if [ "$cg_max" != "max" ] && [ -n "$cg_max" ]; then
  cg_avail=$(( (cg_max - cg_cur + ${cg_file:-0} - ${cg_shmem:-0}) / 1024 ))
  [ "$cg_avail" -lt 0 ] && cg_avail=0
  if [ -z "${avail:-}" ] || [ "$cg_avail" -lt "$avail" ]; then avail="$cg_avail"; fi
fi
if [ -n "${avail:-}" ] && [ "$avail" -lt "$MIN_AVAIL_KB" ]; then
  chains="$(codex_chain_pids | wc -l)"
  deny "Only $((avail / 1024)) MiB available (min of host MemAvailable and the cgroup allowance
memory.max - (memory.current - (file - shmem)); need $((MIN_AVAIL_KB / 1024)) MiB). Starting a Lean build now
is how a shared container OOMs. $chains codex side-process(es) are alive; reclaim those of your
own finished job first (ownership by launch tag and liveness, never by path alone):

  . .claude/hooks/codex-chains.sh
  codex_chains_reapable '<LOOP_JOB_ID of your finished job>'   # inspect
  reap_codex_chains '<LOOP_JOB_ID of your finished job>'       # SIGTERM them

Never \`kill -9\`: an aborting app-server may drop a multi-GB core into its cwd.
Raise LEAN_GUARD_MIN_AVAIL_MIB only after measuring this machine."
fi

exit 0
