# Agent Guidelines

## Core Principles
- Load `.agents/skills/tda-lib-orchestration/SKILL.md` first; its project policy takes precedence over inherited scaffold defaults.
- [CONTRIBUTING.md](CONTRIBUTING.md) is the canonical branch-lifecycle and release/hotfix propagation policy. Keep `develop` and `main` persistent.

## Project Overview
- `tda-lib` is a continuing TDA formalization library with finite persistent homology results and certified F₂ computation, plus bounded Reeb and Mapper theory. See `docs/api.md` and `docs/math/references.md` for exact contracts and review limits. The existing `v0.0.1` and `v0.0.2` releases were infrastructure-only.
- dot owns the private [tda-lib Project](https://github.com/orgs/uda-lab/projects/5) roadmap, milestones, priorities and progress, plus Issue authorization, mathematical decisions and autonomous Codex operation. Issues carry full specifications and execution contracts; read the governing Issue and decisions.

## Commands
```sh
scripts/bootstrap.sh   # cached mathlib + git hooks; never cold-build mathlib
scripts/check.sh       # guarded build, live axiom audit and coverage
scripts/lean.sh lake <args> # mandatory for direct Lean/Lake commands
scripts/lean.sh lean <args> # mandatory for direct Lean invocation
LOOP_JOB_ID=tda-lib/issue-N/role scripts/codex.sh <args> # child Codex
scripts/github-setup.sh # broad labels/settings/ruleset bootstrap; not a targeted repair command
```

Shared runtime safeguards live in `scripts/agent/`. Honor `/tmp/codex-stop`; keep
`LEAN_NUM_THREADS=1` unless the runtime explicitly configures another safe value. Codex
commands must use these entry points regardless of hook activation. Codex and Claude have
optional supported Bash adapters; their activation depends on harness support and trust. See `docs/orchestration.md`.

## Code Conventions
- No unmarked `sorry`/`admit` or custom axioms; Issue-authorized private staging holes on develop obey inherited guards and cannot enter pinned theorem closures or stable releases.
- Never weaken or trivialize statements to close proofs; statement changes need independent source ↔ Lean review.
- Pin every public theorem in its area's append-only `scripts/print_axioms/<Area>.lean`; keep `TDA.lean` and each `TDA/<Area>.lean` aggregator imports-only. Add modules to their owning area aggregator.

## Architecture
- `TDA/` is the library; mathlib is pinned. Research mathlib and TauCeti before introducing duplicate foundations or dependency changes.
- Normal code/documentation work: Issue → topic branch from develop → PR to develop → independent review → applicable check → squash merge. Name the target scope/milestone; a release version may remain `undecided` until release cut. Release/hotfix propagation uses merge-commit PRs under CONTRIBUTING.md, including into develop. Main-first README fixes are incomplete until their intended content reaches develop without losing later work. Never delete either long-lived branch; distinguish content preservation from source ancestry.
- Use normal hosted CI under `.agents/skills/tda-lib-orchestration/SKILL.md` and ADR 0002. Require the existing workflow's `check` to succeed for the evaluated PR head; its change detection determines whether a full build is needed. Existing review and merge authority remain; no direct pushes, routine develop refresh or new parent-approval checkpoint is introduced.
- Project Ready is not execution authorization. dot or an authorized maintainer applies `agent:ready` only after specification, required independent audits, dependencies and validation are verified; no routine human reapproval. `blocked`, `needs-decision`, `do-not-merge` remain hard stops.
- Mathematical sources and conventions belong in `docs/math/`; overall roadmap stays in the Project, execution contracts in Issues. Scratch, logs and review evidence stay out of tracked files.

## Execution defaults
- Base workers use Luna xhigh; difficult mathematics/Lean work may use Sol low/high. Sol high may prepare Issues when dot is unavailable.
- dot considers intake after roughly three hours without observed activity in other repositories, checking competition and dependencies. Two to three disjoint tasks are conditional; Lean builds remain serialized. Other-repository activity holds new intake, rather than interrupting ongoing tasks; ongoing work proceeds through quality-gated PR merge unless legitimately blocked.
- Public API documentation requires doc-gen4; Blueprint is optional, and ellalpha is an independent consumer. The first stable release need not complete every milestone; do not invent dates or a serial milestone order.

## Maintenance Notes
- Keep guidance compact and current; durable decisions belong in `docs/adr/`.
