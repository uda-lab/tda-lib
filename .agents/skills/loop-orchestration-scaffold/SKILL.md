---
name: loop-orchestration-scaffold
description: Continuing Issue-driven library development with independent review, source fidelity, shared resource guards and stable releases across agent harnesses.
---

# Continuing formalization loop

Load `tda-lib-orchestration` first, then apply available `github-loop-engineering`,
`github-driven-workflow`, `lean-formalization-discipline` and `lean-review-routing` skills.
Read their installed instructions; do not assume vendor-specific plugins exist. dot manages
runtime scheduling and models externally. Codex is the primary route; Claude Code can follow
the same procedure. Initialization is complete and there is no single terminal theorem.

## Resume and select

Read the governing Issue and authorized decision comments, current PRs, review findings and
labels. GitHub is the authoritative roadmap, queue and evidence surface. dot may create,
revise and authorize work, including mathematical and dependency decisions. Do not prescribe
roadmap Issue granularity or replace existing Issue templates. Dispatch only ready work with
satisfied dependencies and no hard-stop labels. Keep one driver per lane; serialize Lean builds.

## Execute

Use an Issue branch from `develop`, preferably in `.agents/worktrees/`. Keep disposable
prompts, logs and local review evidence in `.agents/scratch/`, never in tracked documentation.
Read the mathematical source and research mathlib and TauCeti before duplicating foundations.
Make statement contracts explicit where required by the Issue; do not weaken a statement to
finish a proof. Report genuine specification changes on the Issue for dot's ruling.

Use the mandatory shared commands documented in `docs/orchestration.md`: `scripts/lean.sh`
for direct Lean/Lake work and `scripts/codex.sh` for child Codex jobs. Bootstrap, full checks
and axiom audits retain their own shared protection. Honor `/tmp/codex-stop`; stop dependent
work when it exists. Resource limits are operational protection, not a financial budget cap.
Record a distinct `LOOP_JOB_ID=tda-lib/issue-<n>/<role>` on every child job and clean up only
process chains proved to belong to a finished job. Never kill by worktree path, name or broad
process matching. Live or untagged processes are reported, not reclaimed.

Delegate bounded jobs only through available harness facilities; give each job the governing
Issue, inputs, scope, acceptance conditions and reporting route. A reviewer is distinct from
the implementer and read-only. No Claude-only fallback or plugin is required.

## Review and integrate

Run `scripts/check.sh`, local adversarial review, fixes, then PR review as specified by
`lean-review-routing`. Give reviewers the actual source/specification and evaluated head.
Observe all relevant comments and threads; fix or explicitly dispose of findings where they
occur. Changed content needs review covering its new head. No review ceiling waives a blocker.
Merge only a gate-green reviewed PR, bound to the evaluated head; regular PRs target develop.
Remove merged Issue branches and unused worktrees after all owned jobs stop. Keep develop.
No unsolicited messages or notifications to external recipients.

## Source fidelity and releases

When the primary source is unavailable, record the missing source, available evidence and
`digest-based` comparison on the governing Issue. This may permit explicitly authorized
provisional work but never claims primary-source verification. Resolve outstanding source
comparisons before a release that requires them; distinguish verified results from provisional
or excluded results. Public theorem closures remain audited; stable releases exclude staging
holes. An independent source ↔ Lean review records the source, revision, comparison mode and
coverage. Follow project release promotion policy, audit the exact main revision and tag its
results and limitations. Return to the queue afterward.

## References

- `references/orchestrator-tick.md`: a resumable coordination prompt.
- `references/dispatch-prompt.md`: a bounded driver prompt.
- `references/exposition-kickoff.md`, `references/exposition-dispatch.md`,
  `references/note-issue.md`: optional exposition work when requested.
