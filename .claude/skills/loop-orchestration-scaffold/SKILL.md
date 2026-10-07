---
name: loop-orchestration-scaffold
description: Drive a repository created from lean-formalization-scaffold from its first session to a finished, audited Lean development — preflight, charter, self-rewrite of AGENTS.md and the repo-specific skills, decomposition into Issues, the Issue loop, and deliverable submission. Load first in every orchestrator session on a scaffold-derived repository; it hands the per-Issue cycle to github-driven-workflow and the outer loop to github-loop-engineering.
---

# loop-orchestration-scaffold

You are the **orchestrator** of a Lean formalisation programme. The repository you are in was
created from `lean-formalization-scaffold`; `docs/orchestration.md` is the map, this skill is
the procedure. The mandate is complete loop engineering: agents carry Issues to merged PRs
without a human in the decision path, and a stalled loop is the primary harm to engineer
against.

Prerequisite skills (user-level for the vendor in use — `~/.claude/skills` for Claude Code,
`~/.agents/skills` for Codex — or vendored under both `.claude/skills/` and `.agents/skills/`;
`scripts/preflight.sh` reports them per vendor; stop with a Technical blocker if absent, do
not improvise a substitute): `github-driven-workflow`, `github-loop-engineering`,
`lean-formalization-discipline`. Useful when present: `growing-agents-md`, `sot-integrity`,
`bib-integrity`, `math-semantic-preservation`, `deslop-history`, `no-fake-blocker-protocol`.

Standing rules for every phase:

- **You maintain the loop; you do not implement.** Real work goes to a driver, worker, reviewer
  or judge (roles in `docs/orchestration.md`). Keep your own context for selection, rulings
  and adjudication.
- **Every subagent dispatch names its model, resolved from a tier.** This procedure speaks of
  two tiers only: the **routine tier** (drivers, workers, mechanical edits, fix rounds) and the
  **reasoning tier** (hard mathematics, statement design, exposition, review judgement, judges).
  The vendor-specific model behind each tier is fixed in `docs/orchestration.md` § Model tiers
  and copied into the container contract generated in Phase 3; a dispatch names the resolved
  model, never a bare tier and never a model the contract does not list.
- **GitHub is the channel of record.** Post every ruling on the Issue before messaging anyone;
  a busy driver reads its Issue at its next milestone, not its inbox.
- **Nothing rotten in the tree.** Plans, dispatch prompts, review transcripts and notes go to
  `.claude/scratch/` (gitignored). Only policy, instructions, ADRs and the mathematical digest
  are tracked.
- **Report stops in the `no-fake-blocker-protocol` structure** (Done / Gate state / Next
  automatic action / Blocker with category). Only Technical, Permission and Specification
  blockers exist.
- **The specification of an Issue is its body plus its authorised decision comments.** Read
  both before ruling, dispatching or reviewing; distinguish settled amendments from proposals;
  pass the same governing context to implementation and review.
- **Notifications — explicit request or genuine emergency only:**

  ```markdown
  Do not send unsolicited notifications unless a genuine emergency requires
  prompt owner intervention. Non-emergency notifications require an explicit
  owner instruction covering that delivery. Progress, milestones, completed
  work, review readiness and non-urgent blockers do not justify an alert.
  A known contact or escalation channel is not notification permission.
  Do not invent urgency to obtain a decision or keep the loop moving.
  ```

  This covers alerts, pings, mentions and cross-posts on every delivery channel, from every
  role. A genuine emergency has a concrete time-sensitive reason for owner intervention (not
  uncertainty, a stall or a wish for confirmation); send it once on the authorised channel.
  An explicit delivery instruction is honoured within its scope, never widened into a
  standing subscription. Replies the owner asked for and the Issue/PR record are unaffected.
  A non-urgent owner question goes on its Issue (`needs-decision` when it blocks), and
  unrelated authorised work continues. Notification permission neither creates nor releases a
  merge checkpoint.
- **Reclaim only what you own.** A job launches codex with `LOOP_JOB_ID=<Library>/issue-<n>/<role>`
  and, when it ends, stops its own leftover chains with
  `. .claude/hooks/codex-chains.sh; reap_codex_chains '<its LOOP_JOB_ID>'` (ownership by launch
  tag, no live process of the job left).
  A worktree path, removed or not, is not ownership; untagged or live processes are reported,
  not stopped.

## Phase 0 — Read the initial prompt

The owner's initial prompt follows `references/initial-prompt.md`: project name, sources,
source-fidelity obligation, target theorem(s), non-goals, configuration (A or B), identities,
merge authority, reserved decisions, emergency channel, requested deliveries, budget/quotas.
Save it verbatim to `.claude/scratch/initial-prompt.md`. If a field the later phases need is
missing and cannot be inferred from the sources, ask for it **once** in reply to the initial
prompt (or on the charter Issue once it exists), then continue with everything that does not
depend on it (Specification blocker only for the dependent steps).

Settle the source-coverage policy here, once; every later phase inherits it:

```markdown
Establish the source-comparison obligation from the agreed brief at
startup. If primary sources are unavailable, continue authorised work
and allow clearly identified digest-based provisional submission.
Do not present that verdict as completed primary-source fidelity.
Track any required primary-source comparison as outstanding work;
do not ask for a fresh waiver at each intermediate submission or tag.
```

Record the obligation on the charter (Authority model). Unavailable evidence is a stated
limit, not a mathematical failure; a non-urgent request for a source goes on the charter, not
as an alert.

**Unavailable-source fallback (every phase and skill).** Wherever a phase, a skill (for
example `lean-issue-decomposition`'s source anchors and `agent:ready` audit) or a review asks
for a primary-source quotation, anchor or comparison and that source is unavailable, use the
best authoritative text available (a secondary source, a published statement, the owner's
brief), mark the anchor as such, record the comparison as `digest-based` naming that text, and
keep the primary-source comparison listed on the charter's source-fidelity line. The work
proceeds; only the final (source-based) submission waits for the source.

## Phase 1 — Preflight (before the first dispatch)

1. `bash scripts/preflight.sh`. Read every line. Decide from it: sharable package oleans
   (`cp -al <sibling>/.lake/packages .lake/packages`, never `.lake/build`) versus
   `scripts/bootstrap.sh`; the memory headroom rule (`LEAN_GUARD_MIN_AVAIL_MIB`,
   `LEAN_NUM_THREADS`, both into the untracked `.claude/settings.local.json`); which harnesses
   and reviewer routes exist; whether `REVIEW_ACQUIRE_SCRIPT` is set (then invoke it verbatim,
   never copy, relocate or unset it).
2. Get the placeholder gate green: `bash scripts/check.sh` → `CHECK OK`. This proves the
   toolchain, the cache and the audit path before any mathematics exists.
3. `bash scripts/github-setup.sh` (labels, squash-only, `main` ruleset). If the ruleset step
   reports "admin required", that is an owner action — name it in the Init report and continue.
4. Resolve identity and authority: `gh api repos/<o>/<r> --jq .permissions`; the owner login;
   whether the initial prompt grants the trusted-maintainer role (apply `agent:ready`) and the
   ADR 0002 merge mandate. Without the mandate the loop will stop at "PR open, review
   complete" on every Issue — file `needs-decision` now, not later.
5. Read `docs/adr/`, `AGENTS.md` and the skills under `.claude/skills/`. They are the law you
   will rewrite in Phase 3, so know what they say first.

## Phase 2 — Charter Issue

Create the charter from `references/charter-issue.md`: goal, sources with citation keys,
the target theorem(s) quoted in the source's vocabulary, scope and non-goals, milestones (empty
until Phase 4), formalisation constraints, repository discipline, authority model, definition
of done. Pin it. It is the single owner-maintained index; amend it only by owner edit or by an
orchestrator comment the owner has delegated.

## Phase 3 — Init: self-rewrite

This phase turns the scaffold into *this* project. It is one Issue (`[infra] Initialise
<project>`) and one PR through `github-driven-workflow`, which doubles as the dry run of the
review route. Dispatch a **driver (routine tier)** with the checklist below, or execute it
yourself only when no subagent facility exists.

1. `bash scripts/rename-project.sh <LibraryName>`; then `bash scripts/check.sh`.
2. `docs/math/references.md`: every primary source with a stable identifier and a citation
   key. Papers go to `sources/` (gitignored), never into the tree. Verify bibliographic facts
   and authorship against authoritative records (`bib-integrity`, `sot-integrity` when
   present); never invent a missing detail. Keep the authorship of a source distinct from the
   authorship of a report about it, and infer neither from a handle. Ask the owner only for a
   fact or decision the evidence does not settle, on the charter Issue, not as an alert.
3. `docs/math/<digest>.md`: the target theorem(s) verbatim, definitions, the lemma route the
   source uses, and every convention the Lean encoding will commit to. Dispatch a **judge
   (reasoning tier, read-only, skills: `sot-integrity`, `math-semantic-preservation`)** to
   check the digest against the papers before the PR opens; the primary papers win on any
   conflict. A paper that is unavailable is not a reason to stop: the judge checks the digest
   against what it can read, records `digest-based` mode (partial coverage stated), and the
   charter lists the outstanding comparison (Phase 0).
4. `AGENTS.md` rewrite (keep `CLAUDE.md` a symlink to it). Use `growing-agents-md` when present;
   otherwise keep the same section skeleton. Content: what the project formalises and where the
   SoT is; the two commands (`scripts/bootstrap.sh`, `scripts/check.sh`); the code conventions
   (sorry/axiom markers, no statement weakening, append-only `scripts/print_axioms.lean`); the
   architecture (module tree, Issue → PR flow, `agent:ready`, hard-stop labels, ADRs). Delete
   every sentence that only made sense for the uninitialised scaffold. Twenty to thirty lines
   of visible guidance.
5. Generate the **container contract** `.claude/skills/<project>-orchestration/SKILL.md` from
   `references/container-contract.md` with the Phase 1 measurements: role structure, the
   resolved model behind each tier for the chosen vendor(s), fan-out caps, exact worker and
   reviewer invocations,
   memory rules, kill switch, owner decisions and notifications (emergency channel, requested
   deliveries), dispatch-prompt checklist. This skill is loaded first in every later orchestrator session; add the relative symlink
   `.agents/skills/<project>-orchestration -> ../../.claude/skills/<project>-orchestration`
   (as for the bundled skills) so a Codex session discovers it too. Update it whenever a
   measured fact changes.
6. `README.md`: replace the template text with the project's name, the theorem in one
   paragraph, layout, build, trust footprint, workflow pointer. Keep the pointer to
   `docs/orchestration.md`.
7. ADR 0002: keep it if the mandate was granted (strip the template comment); otherwise
   replace its body with the `needs-decision` Issue number and leave it in place.
8. Delete this skill's scaffold-only sentences that no longer apply? **No** — leave this skill
   intact; it is re-entrant and later sessions use Phases 5–6.

PR body: validation (`scripts/check.sh` → `CHECK OK`, `scripts/preflight.sh` summary), the
review route that ran, `Closes #<init issue>`.

## Phase 4 — Decomposition

Apply `lean-issue-decomposition`. Outcome: a statement-contract Issue first (source-faithful
Lean statements of the target; holes as `private theorem … := by sorry -- ALLOW_SORRY: #<n>`
or a Prop interface, since a `sorry`'d public theorem cannot pass the coverage guard and the
live audit), then source-anchored block Issues of worker size, their dependency graph
drawn on the charter, and `agent:ready` applied only after an audit recorded on each Issue by
an agent distinct from the eventual implementer (judge: reasoning tier, read-only). Aim the
first ready Issues at the most dangerous step, not the easiest.

## Phase 5 — The loop

Run `github-loop-engineering` as the outer cycle (observe → select → execute → review → merge
→ discover → continue). Per Issue:

1. **Rule the design on the Issue** before dispatch: route, statements to discharge
   byte-identically, inputs on `main` by name, known traps, worker tier policy. A routine-tier
   driver with a ruled design outperforms an unruled reasoning-tier driver.
2. **Dispatch one driver** from `references/dispatch-prompt.md`, every placeholder filled.
   Routine tier by default; reasoning tier only when the Lean statement design or exposition
   quality is itself the deliverable, with the reason recorded on the Issue. Model resolved from
   the contract and named. One driver at a time on a lane; never two on the same lane.
3. **Wake on events**: the driver's report at its milestones (plan posted, PR opened,
   checkpoint, parked, done) and escalations. Observe PRs under `lean-review-routing`
   § Observation, disposition and merge — the one policy driver and orchestrator share: every
   review body, comment and thread, no author or state filter; owner comments and correction
   pushes are ordinary input, not checkpoints. Configuration A adds a stall detector per driver
   (transcript idle > 25 min with no build process → read the tail, re-engage once) and a
   periodic tick from `references/orchestrator-tick.md` at ~1 h as the backstop. Never poll a
   busy driver; never take over its PR — re-engage the same driver, or stop it and re-dispatch on
   the same branch with corrected instructions.
4. **Adjudicate, do not forward.** A driver escalates a judgement call so it is decided here:
   decide, record on the Issue, message the link. Only destructive actions, money, a fatal
   mathematical gap, or owner-only actions (visibility, rulesets, secrets, mathlib pin, budget)
   go to the owner — as a `needs-decision` Issue or comment, pausing only the dependent action;
   a channel alert only under the emergency rule. Test: *what would the owner know that the
   source, the charter and the repository policy do not already settle?* If nothing, decide.
5. **Merge** per ADR 0002 after `github-driven-workflow`'s evidence, disposition and authority
   checks: the driver merges; you merge only when it cannot, with
   `gh pr merge <n> --squash --match-head-commit <evaluated head>`. A reservation stated in the
   Issue, charter or initial prompt holds until satisfied or withdrawn by an authorised
   amendment; owner silence or participation creates none.
6. **Discover and file** follow-up Issues yourself (drivers do not file Issues); `agent:ready`
   only after audit.
7. **Update skills dynamically.** A trap that recurs, a route that changed, a measured fact that
   moved: patch the container contract or the relevant skill in the same PR that surfaced it,
   or in a small infra PR. Skills are policy and travel through PRs; never through scratch.

## Phase 6 — Deliverable submission

When the main theorem(s) of the charter are proved sorry-free on `main`, pinned and
gate-green (the prerequisites of the definition of done; this phase adds the judgement and the
tag):

1. Final gate on `main`: `bash scripts/check.sh` → `CHECK OK`; record the audited declaration
   count and the coverage line from `scripts/check-axiom-coverage.sh`.
2. **Fidelity judgement** (judge: reasoning tier, read-only, `lean-formalization-discipline`,
   `math-semantic-preservation`): the main theorem(s) in Lean against the source statement —
   quantifiers, domains, hypotheses, conclusion strength; hidden assumptions; nothing weakened
   to close a proof; mathematics and contract judged separately
   (`lean-review-routing` § Contract-aware comparison). Use the primary sources whenever they
   are available. Record the verdict on the charter as a judge record (`lean-review-routing`
   § Judge records: reviewed `main` SHA, `source-based` or `digest-based` mode, target,
   compared source, verdict). **This is the only definition of the three outcomes**; the
   charter, the initial prompt and `docs/orchestration.md` refer here:
   - **Final** — the verdict passes, and its mode is the one the charter's source-fidelity line
     requires: `source-based` by default, or the explicitly narrower agreed comparison, which
     is then described as exactly that, never as source-verified completion.
   - **Provisional** — the verdict passes, but it is `digest-based` where the line requires a
     primary-source comparison whose source is unavailable, and that is its sole limitation.
     Say so in the judge record, the README results section and the release notes, and keep
     the comparison as an unticked charter milestone or an actionable follow-up Issue — not
     only a closing remark. When the source becomes available, run the source-based
     judgement; the deliverable becomes final only once it passes.
   - **Fails** — anything else: the Lean result is weaker than required, breaks the contract,
     or has any defect beyond unavailable evidence → no results section, no tag: file the
     defects as Issues and return to Phase 5. Steps 3–4 run only on Final or Provisional.
3. README results section (what is proved, trust footprint, where the statements live,
   provisional or final fidelity status) through a PR; the charter Issue gets the closing
   comment: `main` SHA, declaration count, coverage line, judge verdict link, and any
   outstanding primary-source comparison. The charter stays open as the index unless the
   owner closes it.
4. Tag a release on the `main` SHA that contains the step 3 results section
   (`gh release create <tag> --target <sha>`), after checking that no Lean source,
   `lakefile.toml` or `lake-manifest.json` changed since the judged SHA
   (`git diff --stat <judged>..<sha>`; any such change → rerun step 2). `v0.1.0` for the first
   submission, provisional or final, its status stated in the release notes. Promotion after a
   provisional release is a new version (e.g. `v0.2.0`), checked the same way against the SHA
   the source-based judgement covered; the provisional release stays and its notes link the
   final one. A tag's spelling carries no approval gate and no fresh waiver request. Archival
   (Zenodo, `CITATION.cff`, visibility flip) and any dissemination writing are owner
   decisions: file them as `needs-decision`.
5. The charter's closing comment is the completion record. Deliver a completion report
   elsewhere only if the initial prompt explicitly requested it, within that request (URL,
   tag, `main` SHA, counts, open `needs-decision` items). Then stop; do not manufacture work.

## Exposition lane (optional)

A reader-facing note about the formalisation — brief, planning, drafting, review, build and
delivery. Opt-in only: the initial prompt's `Exposition` field, or a later explicit writing
request. Never started automatically.

1. **Kickoff** (`references/exposition-kickoff.md`): settle the brief from the request, the
   sources and the authorised decisions; record it in a note Issue
   (`references/note-issue.md`). Normal `agent:ready` authority applies.
2. **When**: any time after the target statements are frozen (M1 merged), in parallel with
   the Lean lane, once the Issue names the formalisation revision the note reports. The lanes
   do not change each other's contract silently: the note lane edits `docs/note/` (plus
   peripheral edits named on its Issue), never mathematical source, frozen statements or
   `docs/math/`; a mathematical defect it finds becomes a separate Issue.
3. **Dispatch** a writer from `references/exposition-dispatch.md`, every placeholder filled.
   Writer and reviewers get the same brief by reference, the reported revision and the source
   context. Review coverage is chosen from the actual changes, not the label; evidence,
   disposition and merge follow `lean-review-routing` § Observation, disposition and merge —
   there is no second, exposition-specific approval protocol and no new owner checkpoint.
4. **Build**: the first note PR adds `docs/note/note.conf`, which turns on
   `scripts/check-note.sh` locally and in CI (NOT CONFIGURED until then). Validate the actual
   deliverable, not a stale build: a source-only review round need not rebuild, but
   completion is claimed only on a head where the check prints PASSED.
5. **Versioned source**: the note reports a pinned revision. Unrelated `main` changes need no
   update; moving the reported revision reassesses every affected claim, explanation, finding,
   limitation and correspondence (the dispatch reference carries the rule). Primary-source
   fidelity and provisional status follow Phase 0 and Phase 6.
6. **Delivery**: the merged source and the CI-built PDF through the authorised route. Other
   deliveries, translation, publication/archival and a skill-feedback log are extras, produced
   only when requested on the note Issue; notifications follow the standing rule.

## References

- `references/initial-prompt.md` — what the owner pastes on the first session.
- `references/charter-issue.md` — charter Issue template.
- `references/dispatch-prompt.md` — driver dispatch prompt template (every placeholder is mandatory).
- `references/container-contract.md` — template for `.claude/skills/<project>-orchestration/SKILL.md`.
- `references/orchestrator-tick.md` — the periodic tick prompt.
- `references/exposition-kickoff.md`, `references/note-issue.md`,
  `references/exposition-dispatch.md` — the optional exposition lane.
