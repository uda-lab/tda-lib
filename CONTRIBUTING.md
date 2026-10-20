# Contributing to tda-lib

## Branches and scope

`develop` is the persistent integration branch. `main` is the stable branch. Keep both
after every PR and release; branch cleanup applies only to finished temporary branches.
Do not use a merge command's source-branch deletion option when its source is `develop`
or `main`. Repository auto-deletion of merged branches must remain disabled.

Every work Issue and PR identifies its target scope or milestone. The existing Project
and governing Issue hold that plan; a branch name does not choose it. A next-release
version may be `undecided` during development. Decide the actual version and included
scope when cutting `release/<version>`; do not infer a version from the last tag or
invent a milestone merely to name a branch.

| Branch role | Starts from | PR destinations | Merge method |
|---|---|---|---|
| Ordinary code or documentation topic | `develop` | `develop` | Squash |
| `release/<version>` | Selected `develop` revision | `main`, then `develop` for release fixes | Merge commit |
| `hotfix/<issue>-<slug>` | `main` or the affected stable revision | `main` and `develop`, or the active release as described below | Merge commit |

Code and documentation normally follow the same topic-branch route, including README
changes. Main-first fixes are bounded stable corrections with the propagation obligations
below. All integrations use PRs and the existing applicable validation and independent review
of the exact head to be merged. No direct or force pushes to the long-lived branches are allowed.

## Ordinary development

Create the Issue branch from `develop`, implement its agreed scope, and open a draft PR
to `develop` until it is ready. Use
`gh pr merge <PR> --squash --match-head-commit <reviewed-head>` after its existing gates pass.
Unrelated changes on `develop` do not require a routine refresh of an otherwise mergeable,
reviewed head. Actual conflicts or source changes require resolution and renewed affected
validation and review. Existing merge authority continues to apply; this policy adds no
parent-approval checkpoint.

## Preparing and completing a release

During preparation, apply the semantic and API criteria in
[lean-review-routing](.agents/skills/lean-review-routing/SKILL.md#semantic-and-api-quality)
to the actual exported API planned for the release. Begin with a bounded representative
API pilot, then record the remaining areas and consumer paths in the governing release
Issue. Inspect characteristic lemmas, meaningful examples, concrete upstream reuse and
hypothesis strength alongside mathematical correctness and public exposition.

Group concrete findings as mathematical correctness, API usability or maintainability.
Apply safe targeted improvements through ordinary develop PRs without weakening statements;
preserve compatibility or document the migration. Reuse completed source-fidelity and
exhaustive audit evidence for the scope it covers. Verify fixes through the existing
applicable checks and independent final-head review. Record exact dependencies for changes
that overlap active packages and continue independent work. This consolidated review and
refactoring is part of the current release preparation; it adds no routine approval stage
or library-wide merge hold. The release Issue records any unresolved findings that affect
the selected scope before the release head is validated.

1. Record the release scope, version and selected `develop` base in the governing Issue.
   Cut `release/<version>` at that base. Stabilization, release metadata and bounded fixes
   belong there; unrelated new work continues on `develop`.
2. Validate and review the actual release head, including every correction made after the
   cut. Merge its PR to `main` with
   `gh pr merge <PR> --merge --match-head-commit <reviewed-release-head>`.
3. Check that the main merge has the reviewed release head as a parent and that its tree
   equals the reviewed release tree before any authorized tag. The original develop base
   need not be an immediate parent: the release branch may contain additional fixes.
4. Propagate release fixes through a merge-commit PR to `develop`. Preserve later correct
   development changes and verify the fixes in the resulting content. If the reviewed
   release head is already in develop's ancestry and there are no unpropagated release or
   main fixes, no extra synchronization PR is needed. Tree equality alone is insufficient.
5. Record the propagation result on the release Issue/PR before closing that work. Remove
   the temporary release branch only after all destinations are accounted for. Keep `develop`.

Release preparation does not itself authorize a main merge, tag or publication outside
the task's existing authority. Conflict resolution that changes reviewed content requires
validation and review of that changed content before the dependent release action.

## Stable hotfixes and main-first documentation fixes

A hotfix carries a bounded correction from stable main through reviewed merge-commit PRs.
Use `--merge --match-head-commit <reviewed-fixing-head>` for its main and propagation PRs.
When an active release exists, merge the hotfix into that release and track its eventual
merge into `develop`; merge it into develop sooner as well if development needs it.
An active-release merge alone does not complete the develop obligation.

This also applies to main-first README or other documentation corrections. The work is
not complete merely because its main PR merged: identify the fixing head and destination
PRs, propagate it, and confirm that the intended text is present on develop while retaining
later correct development additions. Do not replace develop's whole file with an older
version when it has valid additions. A temporary propagation branch may resolve conflicts,
but it must retain the intended source history and receive review of its final head.

Track any outstanding destination as real remaining work in the governing Issue/PR.
Cleanup must not discard a fixing branch before its required propagation is complete.
These obligations apply to stable corrections whether or not they lead to a new tag.

## Content and ancestry are separate checks

`git diff <a> <b> -- <paths>` checks content differences. Equal whole-tree hashes establish
equal snapshots. Neither test establishes that one commit was integrated into the other's
history. A copy or squash can reproduce content without preserving the source commit.

`git merge-base --is-ancestor <fixing-head> <destination-head>` checks history. For a release
merge into main, inspect its parents as well. An ancestor check alone does not show that
conflict resolution retained the fix, so also inspect the affected content or behavior.
Check the actual release/fixing head, not a guessed original develop base. Main's merge
commit need not itself be in develop's ancestry when the fixing branch reached both.

For propagation into an advanced develop branch, verify the intended changes and retention
of later work rather than require develop's entire tree to equal main or the release branch.
Record the reviewed source/destination heads and content/history results in the PR. Do not
claim that a historical content-only port established source ancestry.

## Validation, configuration and further guidance

The [project orchestration policy](.agents/skills/tda-lib-orchestration/SKILL.md) defines
the applicable local checks and normal hosted CI; the
[orchestration guide](docs/orchestration.md) describes execution safeguards and ownership.
Let the existing workflow handle PR and integration pushes. Require its `check` to succeed
for the evaluated PR head, respecting conditional build and documentation steps. Do not add
CI-skip markers to suppress routine validation. Settings updates and release actions require
their own authorization.

The required merge-method configuration is `squash` and `merge` on develop, and `merge`
on main. The former supports ordinary topic squashes and history-preserving propagation.
Keep PR, review, bypass, deletion, force-push and applicable status-check protections intact.
If the actual rules or credentials prevent an authorized propagation merge, report that
blocker; do not squash the propagation or relax other protections to get around it.
`scripts/github-setup.sh` is a broad bootstrap, not a targeted settings-repair command.
Read current settings and limit any authorized update to its exact approved fields.

This policy adapts Vincent Driessen's
[Git branching model](https://nvie.com/posts/a-successful-git-branching-model/): this
repository uses `main`, squash topic PRs and its existing review/resource rules. Its
versioned-release model does not imply automatic deployment or Actions execution.
