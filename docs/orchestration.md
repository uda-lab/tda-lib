# Orchestration guide

Load `.agents/skills/tda-lib-orchestration/SKILL.md` first in every continuing agent session.
It defines continuing TDA library development for dot/Codex and compatible Claude Code
sessions. Initialization is complete; no single final target ends development.

## Authority and roles

dot owns the roadmap, mathematical scope and decisions, Issue creation and authorization,
implementation routing, review, integration, release selection and continuing Codex operation.
The scaffold's orchestrator, driver, worker, independent reviewer and judge roles remain in
use. Issue/PR evidence and independent review remain mandatory; authority does not bypass
integrity gates. The owner has imposed no budget cap. Keep one driver per lane and exclude
concurrent writes to shared build/dependency paths. Runtime scheduling remains external to
this repository. Base workers use Luna xhigh; difficult mathematics/Lean work
may use Sol low/high. Sol high may prepare Issues when dot is unavailable.

## Branches and releases

[CONTRIBUTING.md](../CONTRIBUTING.md) is the canonical lifecycle policy. `develop` and
stable `main` are persistent. Ordinary code/documentation topics start from and target
develop using squash PRs. Release branches start from a selected develop base; release
and hotfix propagation uses merge-commit PRs, including into develop. Explicitly name the
target scope/milestone; the next version may be `undecided` until release cut. The GitHub
default branch does not choose an integration target. Keep both long-lived branches.

A release identifies its develop base, actual reviewed release head and included results,
excludes staging holes, and satisfies the existing release checks/review. The release head
may contain corrections after its base. Its main merge must preserve that actual head as
a parent and match the reviewed release tree before any authorized tag. Content equality
and commit ancestry are separate checks; neither replaces the other. Infrastructure-only
releases make no mathematical-result claims.

Propagate every release/hotfix/main-first documentation correction to develop, directly
or through an active release, and verify both the intended fix and retention of later
development. An active-release destination remains tracked until develop receives it.
No extra synchronization PR is needed only when the relevant release head is already
integrated and no release/main fixes remain unpropagated, not merely when trees match.
dot determines release cadence and versions from actual maturity, scope and API changes.
PR protection, applicable local validation and normal hosted CI remain in force. Require
the existing workflow's `check` to succeed for the evaluated PR head. No direct/force pushes,
long-lived branch deletion or new approval wait.

Each area owns `scripts/print_axioms/<Area>.lean` and the imports-only
`TDA/<Area>.lean` module list. `TDA.lean` imports those lists and `TDA.Basic`.
Append pins and imports in the area that owns a new module; do not edit another area's
list for an independent result. A textually mergeable PR can use its reviewed, validated
head without a gratuitous develop refresh. Actual source overlap or a failed
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
Use [lean-review-routing](../.agents/skills/lean-review-routing/SKILL.md#semantic-and-api-quality)
for semantic and API quality in ordinary reviews. The consolidated review/refactoring in
CONTRIBUTING.md applies the same criteria to the selected release's exported APIs, starting
with a bounded pilot. Define remaining scope and dependencies on the release Issue and link
outstanding review/fix PRs there. Keep detailed pilot results, findings and validation on
those PRs and route targeted fixes through the normal gates.

## Intake and concurrency

dot considers new intake after approximately three hours without observed activity in
other repositories, then checks competing work and dependencies. Two to three disjoint
tasks may run concurrently only when directory or other boundaries clearly separate work,
shared API changes and merge conflicts are unlikely, and resources and review capacity permit;
builds that share mutable paths remain mutually exclusive. Independent builds still need
sufficient resources. When other-repository work starts, hold new intake rather than interrupt
existing tasks. Ongoing tasks continue through quality-gated PR merge unless
legitimately blocked. This is an intake guideline, not a repository-local scheduler.

## Documentation and milestone interpretation

Public API documentation requires doc-gen4. Blueprint is optional; ellalpha is an
independent consumer, not a completion condition. The first stable release need not finish
all Project milestones. Do not invent dates or infer serial execution from milestone order;
dot establishes dependencies and release scope from actual mathematical decisions.

## Prerequisites

The repository vendors four skills under `.agents/skills/`, with compatibility links under
`.claude/skills/`. The companion skills `github-loop-engineering`, `github-driven-workflow`
and `lean-formalization-discipline` come from `t-uda/skills` and are installed per host;
`scripts/preflight.sh` reports which are present; the Claude cloud setup snapshot carries them
at a pinned commit. A host without them reads them from that source. `REVIEW_ACQUIRE_SCRIPT` and the `codex` and `gh` CLIs are host properties as well.
[lean-review-routing](../.agents/skills/lean-review-routing/SKILL.md) gives the review route
for a host that lacks one of them, and [Claude Code cloud setup](claude-cloud-setup.md)
covers hosted sessions.

## Commands and gates

The pre-push hook binds each update to the current HEAD commit and requires a clean tracked
index/worktree plus no untracked build-relevant source. Before diffing, it rejects tracked
paths with a set or named Git `filter` attribute, and blocks if `filter.unset` or
`filter.unspecified` clean/process drivers make the attribute result ambiguous. Clean filters
can hide raw worktree changes. Annotated tags are peeled before comparison; tag updates,
updates to main, a main
checkout and explicit stable mode run the full stable gate. Tag deletions and deletion-only
pushes skip source validation. Manual hook
invocation validates HEAD against origin/develop, falling back to origin/main; an unavailable
base or failed path diff selects the full applicable gate. The hook and hosted CI share the
same NUL-safe path classifier.

The local pre-push coverage pass reports `PIN TYPE ADVISORY` for a newly pinned
public declaration whose elaborated type directly mentions a private constant. It
compares pin names across all area files at the integration merge base. Try restating
the declaration from its area import to assess the client impact. Scoped instances
can also require a client test. These diagnostics leave the gate status unchanged.

The same pass reports `PIN DOC ADVISORY` for new pins whose last name component does not
occur in `docs/api.md` or in the "Unreleased" section of `CHANGELOG.md`. It compares sets of
identifiers and interprets no prose, so it shows a candidate to inspect, not that
documentation is missing or wrong: the result may be covered under another name. It prints
only when the integration merge base is known (`scripts/check.sh` computes it when
`TDA_PIN_ADVISORY_BASE` is unset; an explicitly empty value skips it). No advisory fails a
gate. `scripts/check-released-signatures.sh [<tag>]` (manual, before a release, not part of
any gate; it builds the tag in a temporary worktree from the shared Lake cache) lists pinned
declarations whose elaborated type changed since the last tag, or that disappeared, and says
whether the changelog "Unreleased" section names them. It always exits 0 after a comparison.
`scripts/lean.sh lake env lean scripts/public_theorem_inventory.lean` (manual, outside every
gate) prints a TSV of all public declarations with theorem, pinned, `*Examples`, alias and
first-pass family columns for the downstream-use audit (#1207).
There is no automated check of review on the final head: review authority and the SHA-bound
merge procedure are unchanged (owner decision of 2026-11-24 on #1154).

Issue #982 adds an opt-in remote executor for ordinary gate-required pushes. The default
remains local. Enable an adapter only in this clone's Git config with
`git config --local tda.remoteGate.adapter /absolute/path/to/trusted-adapter`; the resolved
executable must be outside every worktree and the common Git directory. The hook consults
this setting only for ordinary pushes that need a gate. Stable/tag/main updates, deletions
and prose-only pushes keep their existing paths. A configured adapter failure blocks the
push and never falls back to a local pass.

The adapter receives four argv values in order: request JSON, Git source bundle, result JSON
and gate log. It must supervise transport and invoke
`python3 -I <exact-checkout>/scripts/lib/remote-gate.py receive --checkout <dedicated-clean-checkout> --request <request> --bundle <bundle> --result <result> --log <log>`.
The receiver requires the requested exact commit in that already-prepared checkout and never
resets it. It verifies raw tracked bytes, index entries/modes/flags, branch identity, bundle
digest, gate-source identity and a fresh one-use request ID; it holds the canonical resource
locks through before/after checks and the canonical gate. The result binds the actual gate
exit and returned log digest. The request timeout defaults to two hours and is capped at two
hours; `TDA_REMOTE_GATE_TIMEOUT_SECONDS` is an external runtime override for bounded testing
or a measured executor limit. The receiver honors `/tmp/codex-stop` and `CODEX_STOP_FILE`.

The adapter and executor are trusted transport and execution endpoints, not cryptographic
attestation. Keep their addresses, credentials and provisioning only in machine-local
configuration. The adapter must cancel or await its receiver when transport times out; the
receiver terminates only its own gate process group and never claims to clean detached
remote descendants. A remote pass is pre-push feedback, not merge evidence: hosted CI's full
`check` on the evaluated PR head remains authoritative. Protocol fixtures use stub gates and
do not count as Lean or sandbox validation.

`scripts/bootstrap.sh` prepares caches and hooks; `scripts/check.sh` is the full integrity
gate. `scripts/github-setup.sh` is the broad labels/settings/protection bootstrap; do not run
it wholesale for a targeted live setting correction. Read current settings and update only
the approved fields. Develop needs squash and merge methods for its two integration roles;
main uses merge commits. Preserve protections and the existing workflow triggers and
conditional steps. Ordinary PR and integration pushes run CI; do not suppress them with
CI-skip markers. Prose-only changes use focused local checks and the workflow's lightweight
path. Implementation changes run the incremental local gate; the full gate is authoritative
in hosted CI on the evaluated PR head. Optional documentation generation and the note lane
retain their own conditions.
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

For jobs under the same execution account, the wrappers exclude concurrent writes to the same canonical checkout, Lake build or
dependency paths, including symlink targets. Each target has an exclusive lock and its ancestors have shared locks, so overlapping
directory trees conflict while independent descendants can proceed. Missing symlink targets
are included before creation. The wrappers acquire locks in a common order
and retain them across nested checks and documentation generation. Independent worktrees
with separate mutable dependencies do not share a host-wide build lock. The Lake wrapper
accepts this checkout and its docbuild project; project/config redirection is rejected
because it would select resources outside the guarded set. Manifest `lakeDir` and
`packagesDir` select the discovered paths. Explicit Lean outputs (`-o`, `-i`, `-c`, `-b`
and snapshot output options) must stay within these protected resources; temporary fixture
outputs belong under the checkout's ignored scratch directory. Output-shaped arguments
remain conservatively checked with `--run` too. Do not change
dependency/symlink topology during a guarded operation; a detected change requires restarting
the outer gate. Before using the updated wrappers with a shared cache, let jobs using older
wrappers finish: the former `/tmp/lean-build.lock` does not coordinate with path locks.
Do not share writable artifacts through hardlinked copies; use separate copies or visible
symlinked directories whose actual paths the wrappers can lock.

Exclusion protects shared files; it is not a host resource scheduler. Coordinate independent
builds with the other owners according to CPU, memory/cgroup headroom and expected workloads.
A free lock or the headroom probe alone does not establish capacity for another build.
`LEAN_NUM_THREADS` configures each Lean process, separately from the number of concurrent
builds. An explicit positive value is preserved exactly; an unset value stays at the
single-thread default. The CPUs detected as available to the process (affinity, capped by any
cgroup CPU quota) are still reported for visibility, but are not used to raise the default:
each concurrent Lean worker maps a large span of oleans, so raising thread count past what a
host's memory comfortably holds for that many mappings does not shorten a build bound by page
cache for those mappings (#945 measures the related cold-build cost). Raise it explicitly only
on a host whose own measurement supports it, and lower it explicitly after a further measured
OOM (`exit 137`); detection never becomes a fixed hardware fact recorded in this repository.
Cross-account jobs need external coordination; these locks are account-scoped.
`LEAN_GUARD_MIN_AVAIL_MIB` defaults to 1536 and remains configurable. Unavailable
platform metrics are reported as unknown, never as measured spare capacity.
`scripts/bootstrap.sh`, `scripts/check.sh` and axiom audits use the same guarded wrappers.
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

Lake 4.35 artifact caching and full artifact restoration default on in guarded entry points;
explicit environment values, including `false`, are preserved. The cache defaults to the
main checkout's sibling `.cache/<repo>/lake-artifacts`, outside its linked worktrees, and the
resource plan locks it as a shared writable path. To warm a new worktree, run
`scripts/bootstrap.sh` followed by `scripts/check.sh`. `scripts/agent/session-brief.sh`
reports the cache path and runs the guarded `lake build --no-build TDA` freshness probe.
