# Orchestration guide

Load `.agents/skills/tda-lib-orchestration/SKILL.md` first in every continuing Codex session.
It specializes the inherited scaffold procedure for a continuing TDA library; initialization
is complete, and no session should repeat Init or assume one final target ends development.

## Authority and roles

dot owns the roadmap, mathematical scope and decisions, Issue creation and authorization,
implementation routing, review, integration, release selection and continuing Codex operation.
The scaffold's orchestrator, driver, worker, independent reviewer and judge roles remain in
use. Issue/PR evidence and independent review remain mandatory; authority does not bypass
integrity gates. The owner has imposed no budget cap. Preserve scaffold VPS resource defaults,
including serialized Lean builds and one driver per lane. Runtime scheduling and concrete
model selection are managed by dot, not fixed by this repository.

## Branches and releases

Regular Issue branches start from `develop` and PRs target `develop`. The default branch
may remain `main`; explicitly specify the integration base rather than infer it from GitHub's
default. `main` receives reviewed stable promotions only. Both branches require PRs and
`check`; no direct pushes, force pushes or deletion.

A stable promotion identifies its exact develop revision and included results on the Issue
and PR, excludes staging holes, runs the full gate and obtains independent mathematical
review as appropriate. Promote that revision through a PR to main; audit the merged main
revision and tag it with release notes describing results, compatibility and limitations.
The initial infrastructure PR establishes this policy; it is not a mathematical release.

Do not delete `develop` after a promotion; the setup disables automatic branch deletion.
For squash promotions, reconcile develop with the resulting main commit through a reviewed
synchronization PR before later promotions, so release history and subsequent diffs remain
understandable. dot determines release cadence and version numbers from maturity and API changes.

## Evidence and foundations

Read each Issue body and authorized decision comments before implementation and review.
Roadmap intake is via Issues; preserve inherited Issue templates and let dot choose granularity.
`docs/math/` holds durable source-grounded mathematics, not a second work queue.
Research mathlib and TauCeti coverage before choosing foundations; TauCeti is not currently
a dependency. Keep independent source fidelity review for statement changes.

## Commands and gates

`scripts/bootstrap.sh` prepares caches and hooks; `scripts/check.sh` is the full integrity
gate. `scripts/github-setup.sh` installs labels, squash settings and develop/main protections.
Review acquisition and merge evidence follow `github-driven-workflow`; review disposition
follows `lean-review-routing`. All review findings are observed and resolved or disposed of.
No unsolicited notifications; authorized reports and the Issue/PR record are unaffected.
