# 0001 — GitHub coordination with shared agent safeguards

## Decision

GitHub Issues and PRs are the authoritative roadmap, queue, decisions and delivery evidence.
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
