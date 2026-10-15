---
name: tda-lib-orchestration
description: Project entry policy for continuing Codex-driven TDA library development, integration and stable releases.
---

# tda-lib orchestration

Load this skill first. Apply `loop-orchestration-scaffold`, `github-loop-engineering`,
`github-driven-workflow`, `lean-formalization-discipline` and `lean-review-routing` with
this project specialization taking precedence over their template defaults.

## Continuing library contract

Initialization is complete. Do not restart initialization, create a replacement charter,
require one final target, prescribe roadmap Issue granularity or change Issue templates.
The private [tda-lib Project](https://github.com/orgs/uda-lab/projects/5) holds the overall
roadmap, milestones, priorities and progress. Issues carry full mathematical specifications
and execution contracts. Both evolve under dot. The current library has bounded TDA results;
`docs/api.md` and `docs/math/references.md` state their contracts and review limits. The
existing `v0.0.1` and `v0.0.2` releases and the permanent smoke theorem are infrastructure only.

Project Ready does not authorize execution. dot or an authorized maintainer verifies the
specification, required independent audits, dependencies and validation before applying
`agent:ready` to the Issue. No routine human reapproval is required. Existing `blocked`,
`needs-decision` and `do-not-merge` gates remain.

dot has full authority over roadmap and mathematical scope, statement changes, dependency
choices, queue authorization, review routing, merging, releases and autonomous Codex operation.
Inherited owner reservations for mathematical gaps, target changes, mathlib pins, architecture,
model selection and budget do not apply. dot rules on these matters with evidence and records
its decisions on the governing Issue. Existing review, fidelity and soundness gates remain.
Externally unavailable credentials or permissions remain technical blockers for the dependent
action; do not invent mathematical approval checkpoints.

## Integration and release overrides

Use `develop` as the base and target of ordinary Issue PRs, even when main is the GitHub
default. Interpret inherited loop references to inputs on main as inputs on develop.
Stable promotion PRs target main and use merge commits; ordinary develop PRs use squash.
Apply evaluated-head binding and all review gates to both methods. Do not directly push either protected branch.

### Temporary October local-CI exception

Through 2026-10-31 23:59:59 JST, ordinary PRs to `develop` use the Owner-authorized local-CI substitute for the inherited hosted `check` gate. This project-specific exception supersedes inherited hosted-CI merge requirements for `develop` only; it does not change `main` or authorize a stable promotion. For implementation changes, run the full guarded `scripts/check.sh` on the exact final head, retaining the serialized build, live axiom audit, coverage and all applicable Issue acceptance checks. Keep qualifying independent final-head review, resolved findings and threads, no hard-stop labels, and no unchecked PR tasks. Record the evaluated head and base SHAs, exact commands and exit outcomes, audit/coverage summary and review evidence. Focused probes are not a full-check pass. Rebase, conflict resolution or source changes invalidate affected evidence; revalidate and review the actual final head before merge. Use the ordinary develop squash command with `gh pr merge <n> --squash --match-head-commit <evaluated head>`.

Local evidence is never hosted-CI success. Do not dispatch or rerun Actions, trigger an automatic hosted run, add workflows, deploy runners or expand CI. Before publication, require actual disabled-automation evidence or the Owner's explicit setting confirmation; if an unexpected Actions run appears, stop publication and report it. The no-project-budget-cap policy does not authorize hosted CI, CI expansion or disregard of the Owner's resource restriction. The period end is a reevaluation point, not an automatic November restart; do not extend it or change execution mode without an explicit Owner-approved plan.

This exception leaves the #85 docs-job condition and the existing `scripts/build-docs.sh` revision invalidation and exact source-link binding unchanged; optional API docs are not an extra routine `develop` merge gate. The prose-only scope of #89 uses its specified local patch, link, consistency and whitespace checks plus independent exact-head prose review; that narrow validation does not relax the full implementation gate above.

Source-fidelity completion applies to release-scoped results after a stable promotion. Require source fidelity for claimed results, exclude
staging holes from stable releases, audit the exact main revision, then tag and describe its
results and limitations. Do not manufacture a TDA release for the smoke theorem. Release
completion returns to the continuing queue, rather than terminating the program.

## Execution and repository defaults

Codex operation and scheduling are managed by dot. No project budget cap is imposed.
Preserve inherited VPS resource guards, serialized Lean builds, one driver per lane,
independent reviews, process ownership cleanup and notification rules. Resolve actual
available models at dispatch time. Base workers use Luna xhigh; difficult mathematics/Lean
work may use Sol low/high. Sol high may prepare Issues when dot is unavailable. Do not encode
the initialization host's hardware facts in repository policy.

dot considers intake after roughly three hours without observed activity in other
repositories, checking competition and dependencies. Two to three disjoint tasks are
conditional on resources, independence and review capacity; keep Lean builds serialized.
If other-repository work starts, hold new intake rather than interrupt ongoing tasks.
Ongoing work proceeds through quality-gated PR merge unless legitimately blocked.

Public API documentation requires doc-gen4; Blueprint is optional. ellalpha is an independent
consumer, not a completion condition. The first stable release need not finish all Project
milestones. Do not invent dates or impose a serial milestone order.

Research existing mathlib and TauCeti APIs before duplicating foundations; TauCeti becomes
an actual dependency only through a justified infrastructure Issue and reviewed pin.
Theory APIs may be noncomputable; executable verified algorithms have their own contracts.
The repository stays private until roadmap preparation is complete, then dot may publish it
under the owner's standing authorization. English is used for tracked artifacts.

Canonical skills live in `.agents/skills/`; Claude compatibility links point here. Use shared
guarded commands regardless of harness hook activation, as documented in `docs/orchestration.md`.
