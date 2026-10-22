#!/usr/bin/env bash
# PreToolUse(Bash) supplemental guard shared by Codex and Claude native hooks.
#
# Supplemental command-text check for supported native hooks. Runtime wrappers are
# the portable enforcement route. Input: {tool_input: {command: shell text}}.
# Exit 0 allows; exit 2 blocks. Parser checks are conservative, not a shell sandbox.
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
  printf 'LEAN GUARD (scripts/agent/guard.sh) — command blocked.\n\n%s\n' "$1" >&2
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

# Explicit operator stop only; budget is owner-controlled and unlimited.
if printf '%s' "$stripped" | grep -qE 'codex-companion\.mjs|(^|[[:space:];&|(])codex[[:space:]]+(exec|app-server|task|review)'; then
  if [ -e "${CODEX_STOP_FILE:-/tmp/codex-stop}" ]; then
    deny "Codex launch stopped by ${CODEX_STOP_FILE:-/tmp/codex-stop}; do not retry until cleared."
  fi
fi

# --- parse: Lean segments with lock status, self-locking scripts ------------------------
findings="$(printf '%s' "$stripped" | awk -v LOCK="$LOCK" -f "$HERE/lean-cmd-parse.awk")"
[ -z "$findings" ] && exit 0

# --- rule: never wrap a self-locking repository script in an outer flock ---------------
if printf '%s\n' "$findings" | grep -qx 'SELFLOCK 1'; then
  deny "The repository Lean wrappers, bootstrap, audits and check/pre-push gate take \`flock $LOCK\` themselves.
Wrapping them in another flock self-deadlocks: the parent holds the lock and the child
waits for it forever. Run the script bare."
fi

lean_texts="$(printf '%s\n' "$findings" | sed -n 's/^LEAN [01] //p')"

# --- rule 3: no hand-rolled memory/parallelism limits ---------------------------------
if printf '%s\n' "$lean_texts" | grep -qE '(^|[[:space:]])-M[[:space:]]*[0-9]'; then
  deny "\`-M\` sets Lean's own memory ceiling and has repeatedly been set high enough to
OOM a shared container. Drop it. Control parallelism with LEAN_NUM_THREADS instead
(set it in the process environment for this machine)."
fi
if printf '%s\n' "$lean_texts" | grep -qE '(^|[[:space:]])-j[[:space:]]*[0-9]'; then
  deny "Lake 5.x has no \`-j\` flag — it fails with \"unknown short option '-j'\" and the
build never runs. Parallelism is Lean's internal scheduler; control it with
LEAN_NUM_THREADS, not with a lake CLI flag."
fi

# Raw flock cannot prove coverage of a checkout's dependencies. Use guarded entrypoints.
if printf '%s\n' "$findings" | grep -q '^LEAN '; then
  deny "Use scripts/lean.sh for direct Lean/Lake commands. Repository check/bootstrap/audit
wrappers exclude writes to their actual shared build and dependency paths. An outer
flock does not establish resource coverage and must not wrap a self-locking script."
fi

. "$HERE/../lib/resources.sh"
lean_check_headroom || deny "Insufficient memory headroom for Lean."
exit 0
