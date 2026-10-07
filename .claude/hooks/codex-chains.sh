#!/usr/bin/env bash
# Shared helper. Prints the pid of every live codex side-process (app-server broker +
# `codex app-server`). These chains are not reclaimed by the codex plugin when a job ends;
# accumulated chains are the documented cause of OOM waves in small containers.
#
# `pgrep -f 'app-server-broker|codex app-server'` alone is wrong: Claude Code runs each
# Bash tool call through a shell whose argv is the literal command text, so any command
# that merely MENTIONS the pattern matches itself. Filter on /proc/<pid>/comm so only the
# real processes (node running the broker, the codex binary) survive.
codex_chain_pids() {
  local pid comm
  for pid in $(pgrep -f 'app-server-broker\.mjs|codex app-server' 2>/dev/null); do
    comm="$(cat "/proc/$pid/comm" 2>/dev/null || true)"
    case "$comm" in node|codex|codex-*) printf '%s\n' "$pid" ;; esac
  done
}

# Ownership-aware cleanup. A job (driver, worker, reviewer) launches every codex invocation
# with `LOOP_JOB_ID=<Library>/issue-<n>/<role>` in its environment; the broker and
# `codex app-server` it spawns inherit that environment, so the id is launch provenance that
# survives re-parenting. A chain may be stopped only when
#   * ownership: its launch environment carries a job id matching the caller's pattern, and
#   * no continued need: no live process outside the codex chains carries the same id (the
#     job's companion task, worker or a command a chain is running would).
# Untagged chains are never selected: a working directory, deleted or not, is not ownership.

# The LOOP_JOB_ID a process was launched with (empty if none or unreadable).
loop_job_of() {
  { grep -z '^LOOP_JOB_ID=' "/proc/$1/environ" 2>/dev/null || true; } | tr -d '\0' | sed 's/^LOOP_JOB_ID=//' | head -n 1
}

# loop_job_active <job-id> <chain pid>... — true while a non-chain process carries the id.
loop_job_active() {
  local job="$1" p d; shift
  local chains=" $* "
  for d in /proc/[0-9]*; do
    p="${d#/proc/}"
    case "$chains" in *" $p "*) continue ;; esac
    grep -qzx "LOOP_JOB_ID=$job" "$d/environ" 2>/dev/null && return 0
  done
  return 1
}

# codex_chains_reapable <job-glob> [--deleted-cwd-only] — pids of chains of finished jobs.
# <job-glob> is a shell pattern: an exact id for a job's own cleanup, `<Library>/*` for a
# repository-wide sweep. --deleted-cwd-only additionally requires a removed working directory.
codex_chains_reapable() {
  local glob="${1:?job id or pattern}" only_deleted="${2:-}" pid job cwd chains
  if [ -n "${LOOP_JOB_ID:-}" ]; then
    echo "codex_chains_reapable: run without LOOP_JOB_ID in the environment (it would mark the job live)." >&2
    return 2
  fi
  chains="$(codex_chain_pids | tr '\n' ' ')"
  for pid in $chains; do
    job="$(loop_job_of "$pid")"
    [ -n "$job" ] || continue
    # shellcheck disable=SC2254  # the pattern is intentionally a glob
    case "$job" in $glob) ;; *) continue ;; esac
    if [ "$only_deleted" = --deleted-cwd-only ]; then
      cwd="$(readlink "/proc/$pid/cwd" 2>/dev/null || true)"
      case "$cwd" in *' (deleted)') ;; *) continue ;; esac
    fi
    # shellcheck disable=SC2086  # word-split pid list
    loop_job_active "$job" $chains && continue
    printf '%s\n' "$pid"
  done
}

# reap_codex_chains <job-glob> [--deleted-cwd-only] — SIGTERM (never SIGKILL: an aborting
# app-server may drop a multi-GB core) every reapable chain; prints the number signalled.
reap_codex_chains() {
  local n=0 pid list
  list="$(codex_chains_reapable "$@")" || return $?
  for pid in $list; do kill "$pid" 2>/dev/null && n=$((n + 1)); done
  echo "$n"
}
