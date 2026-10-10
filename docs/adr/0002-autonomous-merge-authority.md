# 0002 — Autonomous merge authority on verified gates

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

Repository settings allow squash and merge commits; the develop ruleset allows squash only,
and the main ruleset allows merge commits only. Rebase merges are disabled. Runtime-specific
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

The Owner authorized ordinary `develop` merges using local CI through 2026-10-31 23:59:59 JST. This dated exception substitutes for the hosted `check` gate only on ordinary PRs to `develop`; it does not amend this ADR's stable-promotion policy or `main`'s required `check`. At the 2026-10-10 readback, the active `develop` ruleset retained PR/squash, deletion and non-fast-forward protections with no required status check; the active `main` ruleset remained unchanged and required `check`. The Owner reported that repository Actions were disabled; the available GitHub API integration could not read back that setting.

The first local-CI examples are evidence only for their recorded heads: PR #76 records `scripts/check.sh` and the pre-push gate passing on `db3f442ccfe90b338234c0adc057ac3715234e39`, with its exact-head review and no new Actions run ([record](https://github.com/uda-lab/tda-lib/pull/76#issuecomment-6095605280)); PR #88 records `scripts/test-guards.sh` and lock-held `scripts/check.sh` passing on `895874c5d0648468a8bcc499a06b3f2ef8291be5`, including its axiom/coverage summary and exact-head review ([PR evidence](https://github.com/uda-lab/tda-lib/pull/88)). Neither example validates a later or different head.

For implementation changes, the substitute requires the full guarded `scripts/check.sh` on the exact final head, including the serialized build, live axiom audit and public coverage, plus every applicable Issue acceptance check. Keep qualifying independent final-head review, resolve findings and threads, clear hard-stop labels and unchecked PR tasks, and bind the merge to the evaluated head. Record the evaluated head and base SHAs, exact commands and exit outcomes, audit/coverage summary and review evidence in the PR or Issue. Focused probes do not pass the full gate. Rebase, conflict resolution or source changes invalidate affected evidence; revalidate and review the final head. Keep existing runtime guards and serialized Lean builds. Use `gh pr merge <n> --squash --match-head-commit <evaluated head>` for the final develop merge.

Local results must never be described as hosted-CI success, and no GitHub check or status may be invented. Do not dispatch or rerun Actions, trigger an automatic hosted run, add workflows, deploy runners or expand CI. Before publication, require actual disabled-automation evidence or the Owner's explicit setting confirmation; if an unexpected Actions run appears, stop publication and report it. No project budget cap does not authorize hosted CI, CI expansion or disregard of the Owner's resource restriction. This exception makes no credential or settings changes.

The exception is limited to ordinary `develop` PRs and ends at 2026-10-31 23:59:59 JST. That time is a reevaluation point, not an automatic November restart; do not extend the exception or change execution mode without an explicit Owner-approved plan. This addendum does not authorize a `main` release that cannot satisfy its actual rules. It leaves the #85 docs-job condition and the existing `scripts/build-docs.sh` revision invalidation and exact source-link binding unchanged; optional API docs are not an extra routine `develop` merge gate. For prose-only #89, the Issue's three-file patch, link, consistency and whitespace checks plus independent exact-head prose review suffice; this does not represent Lean, doc-gen4, proof, axiom or coverage checks as run, or relax the implementation gate.
