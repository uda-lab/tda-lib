# Agent Guidelines

## Core Principles
- Load `.agents/skills/tda-lib-orchestration/SKILL.md` first; its project policy takes precedence over inherited scaffold defaults.

## Project Overview
- `tda-lib` is a continuing TDA formalization library, covering theory and verified algorithms; no TDA results are provided yet.
- dot owns the roadmap, Issue queue, mathematical decisions and autonomous Codex operation. Read the governing Issue and decision comments; do not rerun scaffold Init.

## Commands
```sh
scripts/bootstrap.sh   # cached mathlib + git hooks; never cold-build mathlib
scripts/check.sh       # guarded build, live axiom audit and coverage
scripts/lean.sh lake <args> # mandatory for direct Lean/Lake commands
scripts/lean.sh lean <args> # mandatory for direct Lean invocation
LOOP_JOB_ID=tda-lib/issue-N/role scripts/codex.sh <args> # child Codex
scripts/github-setup.sh # labels, squash settings, develop/main rulesets
```

Shared runtime safeguards live in `scripts/agent/`. Honor `/tmp/codex-stop`; keep
`LEAN_NUM_THREADS=1` unless the runtime explicitly configures another safe value. Codex
commands must use these entry points regardless of hook activation. Codex and Claude have
optional supported Bash adapters; their activation depends on harness support and trust. See `docs/orchestration.md`.

## Code Conventions
- No unmarked `sorry`/`admit` or custom axioms; Issue-authorized private staging holes on develop obey inherited guards and cannot enter pinned theorem closures or stable releases.
- Never weaken or trivialize statements to close proofs; statement changes need independent source ↔ Lean review.
- Pin every public theorem in append-only `scripts/print_axioms.lean`; import every module through the imports-only `TDA.lean` aggregator.

## Architecture
- `TDA/` is the library; mathlib is pinned. Research mathlib and TauCeti before introducing duplicate foundations or dependency changes.
- Normal work: Issue → issue branch from develop → PR to develop → independent review → check → squash merge. Stable release promotions use reviewed PRs to main and tags; no direct pushes to either branch.
- dot may authorize Issues with `agent:ready`; `blocked`, `needs-decision`, `do-not-merge` remain hard stops until resolved.
- Mathematical sources and conventions belong in `docs/math/`; roadmap and queue stay in GitHub Issues. Scratch, logs and review evidence stay out of tracked files.

## Maintenance Notes
- Keep guidance compact and current; durable decisions belong in `docs/adr/`.
