# 0001 — GitHub coordination with shared agent safeguards

## Decision

The private [tda-lib Project](https://github.com/orgs/uda-lab/projects/5) holds the overall
roadmap, milestones, priorities and progress. GitHub Issues hold full mathematical
specifications and execution contracts; Issues and PRs record decisions and delivery
evidence. Project Ready alone does not authorize execution: dot or an authorized maintainer
checks specification, required independent audits, dependencies and validation before
applying `agent:ready` to the Issue.
dot manages the continuing Codex runtime externally. Claude Code can use the same project
policy. No repository-local scheduler, state machine or duplicate status ledger is introduced.

Canonical skills live in `.agents/skills/`; `.claude/skills/` contains compatibility symlinks.
Shared safeguards live in `scripts/agent/`, with mandatory Lean and child-Codex command
wrappers. Optional native Codex and Claude hooks adapt supported Bash commands when enabled and
trusted. Agents must use the shared commands independently of hook activation; unsupported
execution routes are not guaranteed to be intercepted.

Disposable prompts, review transcripts, logs and worktrees live under `.agents/scratch/`
and `.agents/worktrees/`, both ignored. Legacy Claude scratch/worktree exclusions remain
for compatibility. Local material is never authoritative coordination state.

## Consequences

A fresh session resumes from GitHub and the canonical skills. Resource protection, stop
handling and ownership-based cleanup are shared across harnesses. The runtime can change
without rewriting mathematical contracts or retaining local coordinator state.
