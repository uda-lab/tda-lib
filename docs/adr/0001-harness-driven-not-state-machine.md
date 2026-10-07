# 0001 — GitHub is the only coordination surface; existing harnesses drive the loop

## Context

Autonomous formalisation loops need coordination between an orchestrator, per-Issue drivers,
workers and reviewers. The source projects (`uda-lab/mobius-cpt`,
`uda-lab/metric-moduli-separability`) ran to completion without any bespoke orchestration
runtime: the vendors' own agent harnesses (Claude Code, Codex CLI/plugin) provided sessions,
subagents, hooks, scheduling and review commands, and GitHub Issues/PRs carried every
decision. Attempts elsewhere to add a repository-local state machine, ledger or scheduler
produced rotten status documents, duplicated GitHub state, and a second thing to debug.

## Decision

- **No custom orchestration runtime, state machine, scheduler or ledger** lives in this
  repository. Roles (orchestrator, driver, worker, reviewer, judge) are abstract and mapped to
  vendor harness facilities in `docs/orchestration.md`; the mapping is configuration, not code.
- **GitHub Issues and PRs are the sole queue, plan and evidence surface.** An Issue with
  `agent:ready` is the unit of work; a PR with review evidence and green gates is the unit of
  delivery; labels `blocked` / `needs-decision` / `do-not-merge` are the only hard stops.
- **Only policy, instructions and ADRs are tracked.** Plans, review transcripts, dispatch
  prompts and work notes live in `.claude/scratch/` (gitignored) and are disposable;
  `scripts/check-transient-artifacts.sh` rejects status-style documents in the tree.
- **Periodic execution uses the harness**: `/loop` or cron + `claude -p` / `codex exec` with the
  tick prompt in the orchestration skill; the loop state is re-derived from GitHub on every tick.

## Consequences

- A fresh session (or a different vendor's harness) resumes from GitHub state alone; nothing
  local is authoritative.
- Repo-specific behaviour is expressed as skills under `.claude/skills/` and as the hooks in
  `.claude/hooks/`, both plain files any harness can read.
- Anything that would require a persistent local coordinator is out of scope by design;
  propose it as `needs-decision`.
