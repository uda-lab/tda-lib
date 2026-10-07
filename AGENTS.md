# Agent Guidelines

<!-- Do not restructure or delete sections. Update individual values in-place when they change. -->

## Core Principles

- Keep this file under 20-30 lines of visible guidance.
- Keep only repo-specific, non-obvious instructions here.

## Project Overview

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- This is an **uninitialised instance of `lean-formalization-scaffold`**: a Lean 4 + mathlib repository with its gates, CI, hooks and orchestration skills in place and **no formalisation target yet**. There is no feature work to do. Do not write mathematics, do not "improve" the placeholder module.
- Your first and only task in this state is **harness preflight and initialisation**: load `.claude/skills/loop-orchestration-scaffold/SKILL.md` and run it from Phase 0 with the owner's initial prompt (`references/initial-prompt.md`). It measures the machine, sets up GitHub, creates the charter Issue, renames the library, digests the sources into `docs/math/`, generates the repo-specific orchestration skill, and **rewrites this file** (and `CLAUDE.md`, a symlink to it) for the project through the first PR. `docs/orchestration.md` is the one-page map of roles and configurations.
- Skills are plain Markdown under `.claude/skills/` (Claude Code discovers them; other harnesses read them as documents). Prerequisites `github-driven-workflow`, `github-loop-engineering`, `lean-formalization-discipline` are expected at user level or vendored; stop with a named blocker if absent.

## Commands

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
~~~sh
scripts/preflight.sh      # measured environment facts; no build, no GitHub mutation
scripts/bootstrap.sh      # idempotent: mathlib oleans + git hooks path; never cold-build mathlib, never `lake update`
scripts/check.sh          # full gate: guards, lake build, live #print axioms, coverage; serialised on /tmp/lean-build.lock
scripts/github-setup.sh   # idempotent labels, squash-only, `main` ruleset
scripts/rename-project.sh <Name>   # Init only: LeanScaffold -> project library name
scripts/check-note.sh     # exposition note build/check; NOT CONFIGURED (skipped) until docs/note/note.conf exists
~~~

## Code Conventions

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- Accepted code has no `sorry`/`admit`; `-- ALLOW_SORRY: #<issue> …` on the same line is the only escape, for work an Issue authorises to land incomplete, and it never reaches a pinned theorem's closure.
- No `axiom`/`constant`/`opaque`/`unsafe`; `-- ALLOW_AXIOM: #<issue> …` passes the textual guard but `scripts/check-axioms.sh` still rejects it (allowlist: propext, Classical.choice, Quot.sound; changing it is `needs-decision`).
- Never weaken, specialise or trivialise a statement to close a proof; statement-changing PRs need a source ↔ Lean review by an agent distinct from the implementer.
- Every public theorem a PR claims is appended to `scripts/print_axioms.lean` (append-only; enforced by the coverage guard).
- Proof experiments, logs, plans and notes stay untracked (`.claude/scratch/`); the transient-artefact guard rejects status/roadmap/handoff-style documents.

## Architecture

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- `LeanScaffold/` module tree with root aggregator `LeanScaffold.lean` (renamed in Init); mathlib pinned by tag in `lakefile.toml` and by commit in `lake-manifest.json` (bumping is an infrastructure Issue).
- Flow: Issue → `issue-<n>-<slug>` branch → PR (`Closes #n`, no unchecked boxes) → independent review → CI job `check` → squash merge; no direct pushes to `main`.
- The root aggregator is imports-only; theorems and definitions go in modules under the library directory (`scripts/check-root-aggregator.sh`, run by `scripts/check.sh`).
- `agent:ready` is the execution-authorisation label, applied only by the owner or the trusted maintainer after auditing scope and acceptance; `blocked`, `needs-decision`, `do-not-merge` are hard stops.
- Durable decisions go to `docs/adr/`, mathematical statements to `docs/math/`; everything else lives in Issues and PRs. No orchestration runtime or state machine lives here (ADR 0001).

## Maintenance Notes

<!-- This section is permanent. Do not delete. -->
- Delete stale or inferable guidance.
- Update commands and architecture when workflows change.
- Keep durable rules here; move detail to dedicated docs.
