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
