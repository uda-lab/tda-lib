# 0002 — Autonomous merge authority on verified gates

The original decision and its dated addenda are retained below. The 2026-10-16 lifecycle
addendum and [CONTRIBUTING.md](../../CONTRIBUTING.md) define branch roles and merge methods.
The 2026-10-17 CI addendum restores normal hosted CI and supersedes the October local-CI
exception. Existing merge authority and integrity gates remain.

## Context

The flow is Issue → branch → PR → independent review → CI job `check` → branch-appropriate merge, with no
direct pushes to `develop` or `main`. Without explicit merge authority a fully autonomous loop stalls at
"PR open" after every Issue, and a merge-ready PR left idle was the primary failure mode
observed on the source projects. Session tooling (permission classifiers) has also refused a
driver's `gh pr merge` while allowing the identical command earlier, so the authority must be
held by more than one tier.

## Decision

The owner delegates roadmap, mathematical decisions, queue authorization and continuing
Codex development to dot, with no project budget cap. Regular PRs target develop; stable
promotions target main and receive release tags.

The owner grants both the per-Issue driver and the orchestrator permanent, pre-authorised
authority to merge a PR whose gates are verified:

- CI `check` green on the head commit;
- `github-driven-workflow` §8: qualifying independent review evidence covering the final
  change, blocking findings fixed and verified or disposed of (`lean-review-routing`), and
  the merge within this authority and any decision the governing Issue or charter reserves;
- no `do-not-merge`, `blocked` or `needs-decision` label; no unresolved review thread; no
  unchecked task box in the PR body.

The driver merges its own PR; the orchestrator may merge when the driver cannot. Ordinary
PRs to develop use `gh pr merge <n> --squash --match-head-commit <evaluated head>`.
Stable promotions to main use `gh pr merge <n> --merge --match-head-commit <evaluated head>`.
The main merge preserves the released develop head as a parent; verify that its tree matches
the reviewed release tree before tagging. Squashing a stable promotion would lose that
ancestry and cause later promotion comparisons to repeat already released changes.

Repository policy allows squash and merge commits on develop for its respective branch
roles, and merge commits on main. Verify the actual settings and rules; policy is not proof
of their deployment. Rebase merges are disabled. Runtime-specific
permission configuration is external; authorization does not bypass branch protection,
review or integrity checks.

## Consequences

- Branch protection, the guards and CI remain the actual gates; merge authority adds no gate
  and removes none.
- A merge past an undisposed substantive finding, a red gate, a hard-stop label or a reserved
  owner decision remains prohibited. Owner comments and corrections are ordinary review input;
  they create no checkpoint that the Issue or charter did not already reserve.
- A merge-ready PR is merged promptly; leaving it idle is the failure.

## Addendum — 2026-10-10: temporary local-CI merges to develop

**Historical record, superseded on 2026-10-17 by the CI addendum below.** The dated
permissions, prohibitions and October end date in this section no longer govern execution.

The Owner authorized ordinary `develop` merges using local CI through 2026-10-31 23:59:59 JST. This dated exception substitutes for the hosted `check` gate only on ordinary PRs to `develop`; it does not amend this ADR's stable-promotion policy or `main`'s required `check`. At the 2026-10-10 readback, the active `develop` ruleset retained PR/squash, deletion and non-fast-forward protections with no required status check; the active `main` ruleset remained unchanged and required `check`. The Owner reported that repository Actions were disabled; the available GitHub API integration could not read back that setting.

The first local-CI examples are evidence only for their recorded heads: PR #76 records `scripts/check.sh` and the pre-push gate passing on `db3f442ccfe90b338234c0adc057ac3715234e39`, with its exact-head review and no new Actions run ([record](https://github.com/uda-lab/tda-lib/pull/76#issuecomment-6095605280)); PR #88 records `scripts/test-guards.sh` and lock-held `scripts/check.sh` passing on `895874c5d0648468a8bcc499a06b3f2ef8291be5`, including its axiom/coverage summary and exact-head review ([PR evidence](https://github.com/uda-lab/tda-lib/pull/88)). Neither example validates a later or different head.

For implementation changes, the substitute requires the full guarded `scripts/check.sh` on the exact final head, including the serialized build, live axiom audit and public coverage, plus every applicable Issue acceptance check. Keep qualifying independent final-head review, resolve findings and threads, clear hard-stop labels and unchecked PR tasks, and bind the merge to the evaluated head. Record the evaluated head and base SHAs, exact commands and exit outcomes, audit/coverage summary and review evidence in the PR or Issue. Focused probes do not pass the full gate. Rebase, conflict resolution or source changes invalidate affected evidence; revalidate and review the final head. Keep existing runtime guards and serialized Lean builds. Use `gh pr merge <n> --squash --match-head-commit <evaluated head>` for the final develop merge.

Local results must never be described as hosted-CI success, and no GitHub check or status may be invented. Do not dispatch or rerun Actions, trigger an automatic hosted run, add workflows, deploy runners or expand CI. Before publication, require actual disabled-automation evidence or the Owner's explicit setting confirmation; if an unexpected Actions run appears, stop publication and report it. No project budget cap does not authorize hosted CI, CI expansion or disregard of the Owner's resource restriction. This exception makes no credential or settings changes.

The exception is limited to ordinary `develop` PRs and ends at 2026-10-31 23:59:59 JST. That time is a reevaluation point, not an automatic November restart; do not extend the exception or change execution mode without an explicit Owner-approved plan. This addendum does not authorize a `main` release that cannot satisfy its actual rules. It leaves the #85 docs-job condition and the existing `scripts/build-docs.sh` revision invalidation and exact source-link binding unchanged; optional API docs are not an extra routine `develop` merge gate. For prose-only #89, the Issue's three-file patch, link, consistency and whitespace checks plus independent exact-head prose review suffice; this does not represent Lean, doc-gen4, proof, axiom or coverage checks as run, or relax the implementation gate.

## Addendum — 2026-10-16: persistent integration and propagation

The Owner adopts the branch lifecycle in CONTRIBUTING.md: persistent develop and stable
main; ordinary code/documentation topic squashes into develop; release/<version> branches
from a selected develop base; and merge-commit release/hotfix propagation to all required
destinations. Main-first README fixes require verified develop propagation as well. An
active release may carry a hotfix, with its final develop destination kept outstanding
until completed. The next target scope/milestone is explicit; a version may remain
undecided until release cut, when its version and scope are fixed.

The reviewed release head, including any post-cut fixes, is the required source parent
of its main merge. Equal trees establish content equality, not integration ancestry;
ancestry also needs a content-preservation check after conflict resolution. The original
develop base need not be an immediate main parent. Both long-lived branches survive
release/PR cleanup. A matching tree alone does not waive propagation.

The Owner authorizes develop's allowed merge methods to be squash and merge, retaining
the PR requirement and all other rule parameters, conditions and bypass/deletion/force-push
protections. Repository merge commits are already enabled; main's methods and other live
settings are unchanged by this decision. Verify any authorized targeted update against
the latest readback; the policy text is not proof of its deployment. Do not run the broad
bootstrap to apply a single-field correction.

At adoption, this retained the existing exact-head review/validation requirements and the
then-current October Actions restriction; the 2026-10-17 addendum supersedes that restriction.
It introduces no universal develop refresh, new gate or parent-approval wait, and does not
itself initiate a main merge, release or tag.

## Addendum — 2026-10-17: normal hosted CI restored

The Owner lifted the CI restriction for `uda-lab/tda-lib` in [#315](https://github.com/uda-lab/tda-lib/issues/315).
Use normal hosted CI immediately. The 2026-10-10 exception, its October deadline, prohibition
on ordinary Actions and disabled-automation evidence requirement are superseded. Local-only
clauses in existing execution contracts are replaced by applicable local validation and
successful hosted `check` on the evaluated PR head. No mandatory CI-skip marker remains.

Keep the existing workflow's PR, integration-push and manual triggers, build-change detection,
docs-job condition and opt-in note lane. Prose-only changes may pass its lightweight check
without a Lean build. Implementation changes retain the guarded local build, live axiom
audit and coverage, plus applicable hosted build steps. Do not add redundant full builds or
full doc generation. Independent exact-head review, feedback disposition, branch protections
and expected-head merge authority remain. This decision changes no credentials, permissions,
protections or repository settings, and authorizes no main merge, release or publication.

The ordinary-PR measurement [38991899532](https://github.com/uda-lab/tda-lib/actions/runs/38991899532)
succeeded on source head `6bd0ab353d8c943545d71e9aac5c7da5c6835cd7`: `check` took 27m53s,
including a 25m41s full gate, on Ubuntu 24.04.5 LTS. Cached mathlib was restored; docs were
skipped and no exposition note was configured. It validates that measured head, not the
later final head of #309 or subsequent changes; detailed steps remain in the PR evidence.

The legacy run-usage API returned zero billable milliseconds, which does not establish
zero invoice cost. Organization billing usage and repository Actions-setting reads returned
`403 Resource not accessible by integration`; net charges, credits and included minutes
could not be verified. The restoration follows the Owner's instruction, without assuming
free future runs or changing access to obtain billing data.
