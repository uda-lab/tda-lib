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

Read [CONTRIBUTING.md](../../../CONTRIBUTING.md) for the canonical branch lifecycle.
Keep develop and main persistent; never use source-branch deletion on either. Ordinary
code/documentation Issue topics use develop as base and target, even when main is the
GitHub default, and merge by squash. Interpret inherited ordinary-loop references to
inputs on main as inputs on develop. Release/hotfix propagation uses merge commits,
including into develop; main stable corrections/promotions use merge commits as well.
Apply evaluated-head binding and existing review/validation gates to both methods.

State the next target scope/milestone in the governing Issue/Project. A release version
may be undecided before release cut, when the actual version and included scope are fixed.
Apply `lean-review-routing` § Semantic and API quality now and during CONTRIBUTING.md's
pre-release consolidated review/refactoring. Keep pilot results, concrete findings and
validation evidence on the normal PRs; the governing release Issue defines the remaining
exported-API scope and dependencies and links outstanding review/fix PRs. Use the existing gates.
The actual reviewed release head may include fixes after its develop base; preserve that
head as a main-merge parent and verify the reviewed tree before any authorized tag.
Propagate release/hotfix/main-first README corrections and verify intended content on
develop without losing later additions. An active release must track the eventual develop
destination. Tree equality is not ancestry, and ancestry does not prove content retention.
Do not impose ordinary-PR refreshes or a new parent-approval checkpoint. No direct pushes.

### CI and validation

Use normal hosted CI for this repository. The Owner lifted the October restriction;
ADR 0002 retains the superseded exception as history. Let the existing workflow run on
PRs and pushes to `develop` and `main`, and require its `check` to succeed for the evaluated
PR head before merge. Do not add CI-skip markers to suppress routine validation or use a
local result as a replacement for hosted success. Observe actual checks and branch rules;
never invent a status.

Run applicable local checks and the mandatory pre-push gate. Implementation changes retain
the full guarded `scripts/check.sh`, shared-path exclusion, live axiom audit, public coverage and
Issue acceptance checks. For prose-only changes, use focused patch, link, consistency and
whitespace checks plus the existing textual guards; let workflow change detection select
the hosted build steps. Do not add redundant full builds or full doc generation.

Keep independent final-head review, resolved findings and threads, no hard-stop labels and
no unchecked PR tasks. Record evaluated head/base SHAs, exact commands and exit outcomes,
applicable audit/coverage results, the hosted run and review evidence in the PR. Rebase,
conflict resolution or source changes invalidate affected evidence; validate and review the
actual final head. Merge ordinary develop topics with
`gh pr merge <n> --squash --match-head-commit <evaluated head>`.

Keep the existing docs-job condition and `scripts/build-docs.sh` revision invalidation and
exact source-link binding. Optional API docs are not an extra routine develop merge gate;
the exposition-note lane remains opt-in. Restoring CI authorizes no credential, permission,
protection, repository-setting, workflow-trigger, release or publication change.

Source-fidelity completion applies to release-scoped results after a stable promotion. Require source fidelity for claimed results, exclude
staging holes from stable releases, audit the exact main revision, then tag and describe its
results and limitations. Do not manufacture a TDA release for the smoke theorem. Release
completion returns to the continuing queue, rather than terminating the program.

## Execution and repository defaults

Codex operation and scheduling are managed by dot. No project budget cap is imposed.
Preserve memory/headroom and stop guards, exclusion for shared mutable build/dependency paths,
one driver per lane, independent reviews, process ownership cleanup and notification rules. Resolve actual
available models at dispatch time. Base workers use Luna xhigh; difficult mathematics/Lean
work may use Sol low/high. Sol high may prepare Issues when dot is unavailable. Do not encode
the initialization host's hardware facts in repository policy.

dot considers intake after roughly three hours without observed activity in other
repositories, checking competition and dependencies. Two to three disjoint tasks are
conditional on resources, independence and review capacity. Exclude writes to shared
build/dependency paths; coordinate independent builds for actual resource capacity.
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
