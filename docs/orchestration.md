# Orchestration guide

Load `.agents/skills/tda-lib-orchestration/SKILL.md` first in every continuing agent session.
It defines continuing TDA library development for dot/Codex and compatible Claude Code
sessions. Initialization is complete; no single final target ends development.

## Authority and roles

dot owns the roadmap, mathematical scope and decisions, Issue creation and authorization,
implementation routing, review, integration, release selection and continuing Codex operation.
The scaffold's orchestrator, driver, worker, independent reviewer and judge roles remain in
use. Issue/PR evidence and independent review remain mandatory; authority does not bypass
integrity gates. The owner has imposed no budget cap. Preserve scaffold VPS resource defaults,
including serialized Lean builds and one driver per lane. Runtime scheduling remains
external to this repository. Base workers use Luna xhigh; difficult mathematics/Lean work
may use Sol low/high. Sol high may prepare Issues when dot is unavailable.

## Branches and releases

Regular Issue branches start from `develop` and PRs target `develop`. The default branch
may remain `main`; explicitly specify the integration base rather than infer it from GitHub's
default. `main` receives reviewed stable promotions only. Both branches require PRs and
`check`; no direct pushes, force pushes or deletion.

A stable promotion identifies its exact develop revision and included results on the Issue
and PR, excludes staging holes, runs the full gate and obtains independent mathematical
review as appropriate. Promote that revision through a PR to main; audit the merged main
revision and tag it with release notes describing results, compatibility and limitations.
Infrastructure-only releases make no mathematical-result claims.

Ordinary develop PRs use squash merges. Stable main promotions use merge commits, preserving
the exact released develop head as a parent. The merged main tree must equal the reviewed
release tree before tagging. This ancestry keeps later promotion diffs limited to new work;
no synchronization PR is needed when release trees match. Resolve and review any actual
main/develop content divergence before promotion. Keep develop after each release.
dot determines release cadence and version numbers from maturity and API changes.

Each area owns `scripts/print_axioms/<Area>.lean` and the imports-only
`TDA/<Area>.lean` module list. `TDA.lean` imports those lists and `TDA.Basic`.
Append pins and imports in the area that owns a new module; do not edit another area's
list for an independent result. A textually mergeable PR can use its reviewed, locally
validated head without a gratuitous develop refresh. Actual source overlap or a failed
integrated build needs resolution and renewed validation of the changed head.

## Evidence and foundations

Read each Issue body and authorized decision comments before implementation and review.
The private [tda-lib Project](https://github.com/orgs/uda-lab/projects/5) holds the overall
roadmap, milestones, priorities and progress. Issues hold full mathematical specifications
and execution contracts: theorem statements, assumptions, sources, natural-language proofs,
Lean APIs, dependencies and validation conditions. Preserve inherited templates and let dot
choose granularity. Implementers may open follow-up Issues and bug reports.
Project Ready is a planning status, not execution authorization. dot or an authorized
maintainer verifies specification, required independent audits, dependencies and validation
before applying `agent:ready` to the Issue. No routine human reapproval is required;
`blocked`, `needs-decision` and `do-not-merge` remain hard stops.
`docs/math/` holds durable source-grounded mathematics, not a second work queue.
Research mathlib and TauCeti coverage before choosing foundations; TauCeti is not currently
a dependency. Keep independent source fidelity review for statement changes.

## Intake and concurrency

dot considers new intake after approximately three hours without observed activity in
other repositories, then checks competing work and dependencies. Two to three disjoint
tasks may run concurrently only when directory or other boundaries clearly separate work,
shared API changes and merge conflicts are unlikely, and resources and review capacity permit;
Lean builds remain serialized. When other-repository work starts, hold new intake rather
than interrupt existing tasks. Ongoing tasks continue through quality-gated PR merge unless
legitimately blocked. This is an intake guideline, not a repository-local scheduler.

## Documentation and milestone interpretation

Public API documentation requires doc-gen4. Blueprint is optional; ellalpha is an
independent consumer, not a completion condition. The first stable release need not finish
all Project milestones. Do not invent dates or infer serial execution from milestone order;
dot establishes dependencies and release scope from actual mathematical decisions.

## Commands and gates

`scripts/bootstrap.sh` prepares caches and hooks; `scripts/check.sh` is the full integrity
gate. `scripts/github-setup.sh` installs labels, squash settings and develop/main protections.
Review acquisition and merge evidence follow `github-driven-workflow`; review disposition
follows `lean-review-routing`. All review findings are observed and resolved or disposed of.
No unsolicited notifications; authorized reports and the Issue/PR record are unaffected.

## Shared execution safeguards

Canonical skills are real directories in `.agents/skills/`; `.claude/skills/` links to them.
Use these entry points in every harness:

```sh
scripts/lean.sh lake build
scripts/lean.sh lean <file.lean>
LOOP_JOB_ID=tda-lib/issue-<n>/worker scripts/codex.sh exec <arguments>
scripts/agent/session-brief.sh
```

The shared runtime serializes Lean builds, checks memory headroom and honors
`/tmp/codex-stop`. Defaults are `LEAN_NUM_THREADS=1` and
`LEAN_GUARD_MIN_AVAIL_MIB=1536`; runtime configuration may adapt them to available hardware.
`scripts/bootstrap.sh`, `scripts/check.sh` and axiom audits invoke shared protection directly.
The stop file blocks guarded Lean work and new child Codex launches; remove it only when
the stopping condition has been resolved. It does not terminate existing jobs automatically.

Optional native adapters live in `.claude/settings.json` and `.codex/hooks.json`. They
protect supported Bash command events when the harness supports them and the project hooks
are enabled and trusted. Codex hook activation and trust follow the
[official hook documentation](https://learn.chatgpt.com/docs/hooks). Shared command wrappers
remain mandatory independently of hook activation; arbitrary commands and unsupported
execution routes are not guaranteed to be intercepted. Do not bypass wrappers with
raw build commands. Use the same entry points in linked worktrees; no per-worktree Claude
hook installation is required for these shared commands.

Each child Codex job has a distinct `LOOP_JOB_ID=tda-lib/issue-<n>/<role>`. After its workers
and reviewers finish, source `scripts/agent/codex-chains.sh` and invoke
`reap_codex_chains '<finished job id>'` without that job id in the cleanup caller's environment.
Reclaim only proven finished owned chains. Never terminate live or untagged processes, or
use a worktree path as proof of ownership. Remove unused worktrees and merged Issue branches
after owned jobs finish. Shared disposable paths are `.agents/scratch/` and
`.agents/worktrees/`; legacy Claude paths remain ignored for compatibility.

There is no repository-local dot configuration or scheduler, and no financial budget cap.
Runtime scheduling, available models and autonomous operation remain dot's responsibility.
