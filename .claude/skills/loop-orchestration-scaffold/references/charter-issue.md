# Charter Issue template

Title: `[Charter] Formalise <theorem> from <source key>`. Labels: `priority:P0`; `agent:ready`
once the authority model below is confirmed. Pin it. It is the only owner-maintained index of
the programme; milestones are appended in Phase 4 and ticked as PRs merge.

```markdown
## Goal
Formalise <theorem, cited as in the source> in Lean 4 + mathlib. Primary source: <[KEY] full
reference, identifier>. Secondary sources: <…>. The digest `docs/math/<digest>.md` is the working
mathematical source of truth; the primary papers win on any conflict.

## Target statement (source vocabulary)
<the theorem quoted verbatim, with the source's hypotheses and conventions; if the primary
source is unavailable, quoted from the best authoritative text available and marked as such>

## Scope
<what the programme covers: the theorem, the lemma route, required companions>

Out of scope: <downstream results, optional extensions, alternative proofs>.

## Milestones
<!-- Filled in Phase 4; one line per Issue, ticked on merge. -->
- [ ] M1 — source-faithful Lean statement and dependency boundary (#n)
- [ ] M2 — …

## Formalisation constraints
- No `sorry`, project axioms, or vacuous reformulations in accepted code; `ALLOW_SORRY: #<n>`
  only where an Issue authorises landing incomplete; axiom closure ⊆ {propext, Classical.choice, Quot.sound}.
- Never weaken, specialise or trivialise a source statement to close a proof; statement-changing
  PRs get an independent source ↔ Lean review.
- <source-specific: hypotheses that must be preserved exactly, conventions, forbidden shortcuts>

## Repository discipline
GitHub Issues/PRs are the only queue, plan and evidence surface. No status, roadmap, handoff or
progress files in the tree. Durable decisions go to `docs/adr/`.

## Authority model
- Owner: @<owner>. Trusted AI maintainer(s): @<maintainer>. Only these apply `agent:ready`.
- Agent-created Issues are backlog until an authorised maintainer audits scope and acceptance
  criteria and applies `agent:ready`. For source-sensitive Issues an agent distinct from the
  implementer first audits the source against the literal claim and records it on the Issue.
- `needs-decision` is mandatory for anything changing mathematical scope, the main theorem
  statement, repository architecture, credentials or budget. `blocked`, `needs-decision`,
  `do-not-merge` are hard stops.
- Source fidelity: <the comparison the deliverable requires — the primary sources by default,
  or an explicitly narrower one — and any required source currently unavailable>. Outcomes
  (final / provisional / fails) as defined in `loop-orchestration-scaffold` Phase 6 step 2.
- Merge authority: <granted per docs/adr/0002 | pending #n>. Reserved owner decisions:
  <none | the specific approvals required before a merge>. Owner participation alone creates
  no further checkpoint.
- Owner questions are recorded here or on their Issue; no unsolicited notifications except a
  genuine emergency; requested deliveries: <none | as instructed>.
- Concurrency: one Issue in flight per lane; <n> lanes.

## Definition of done
`<Library>.<main theorem>` proved sorry-free on `main`, pinned in `scripts/print_axioms.lean`,
`scripts/check.sh` green; then (Phase 6) a passing fidelity judgement recorded on this Issue
and a tagged release — final or provisional as defined in Phase 6 step 2; a failing
judgement returns the work to the loop.
```
