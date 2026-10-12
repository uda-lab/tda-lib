---
name: lean-review-routing
description: Review order, reviewer routes per vendor, observation and disposition of review feedback, contract-aware source ↔ Lean comparison and round ceiling for PRs in a Lean formalisation loop — conditional local adversarial review before the PR, broker review evidence on the PR, evidence placement, substantive-versus-not classification, the merge decision delegated to github-driven-workflow's evidence/disposition/authority checks, judge records, five-round ceiling. Use by drivers before opening a PR and after every review round, and by orchestrators when observing PRs, merging or changing routes.
---

# lean-review-routing

Order: **gate → (conditional local review) → open the PR → broker review rounds → merge.**
Never run a local and an external review concurrently: the external one gets spent on defects
the local pass would have caught.

## Evidence placement

Evidence lives where GitHub already records it. The PR body carries one validation block
(evaluated head and base SHAs, exact commands, exit outcomes, axiom and coverage summary),
updated in place for each new head rather than appended as comments. Findings and their
dispositions live in the PR's review threads or one grouped PR comment. The governing Issue
receives one short pickup line, one closing pointer to the squash commit, and only the
reports this loop requires of the driver: a genuine specification change for dot's ruling,
or a missing-source record under the source-fidelity policy. Nothing else goes there (no
scratch source, hashes, probe narratives, progress or chronology). The commit SHA and the
PR's Review events identify the evidence; do not restate them in prose.

## Local review (conditional, before the PR)

Run one local read-only adversarial pass only when the governing Issue requires it, when the
PR adds or changes public statements against a frozen source interface, or when the diff is
large enough that the external round would be spent on mechanical defects. Otherwise skip
it: the broker review is the review. When run, its findings are fixed before the PR and its
report is not posted anywhere.

Frame it as **numbered, falsifiable risks**, never "review this" (a generic prompt returns
"no major issues" on diffs with real defects). Always include:

1. no statement was weakened, specialised or trivialised and no conclusion narrowed; the
   required public name and type, where the contract freezes them, are unchanged (compare
   against the contract text byte for byte); an omitted source hypothesis is classified per
   § Contract-aware comparison, not assumed harmless or fatal;
2. no proxy hypothesis replaced a source hypothesis (bounded for compact, separable for
   Polish, …);
3. every claimed public theorem is appended to `scripts/print_axioms.lean`;
4. no `sorry`/`axiom` outside an Issue-authorised `ALLOW_` marker;
5. no transient artefact, bookkeeping or chronology added to the tree;
6. the Issue's own traps.

Give every reviewer and judge the same governing specification as the implementer: the Issue
body and its authorised decision comments (quoted or linked), not a summary.

Put `git diff develop...HEAD` inside the prompt file (statements only, and say so, if the diff
exceeds the argument limit) and state what the gate already verified so the pass is not spent
re-running it. Read the result in the same turn.

Use a fresh read-only reviewer session or subagent distinct from the implementer. A child
Codex route uses the shared launcher, with a distinct owned job identity:

```sh
LOOP_JOB_ID=tda-lib/issue-<n>/review scripts/codex.sh exec -C <worktree> --sandbox read-only -m <available-model> - < .agents/scratch/local-review-issue-<n>.md
```

Resolve model and effort using dot's runtime. Claude Code may use its available read-only
reviewer facility under the same identity. No plugin is required.

## PR review (evidence for `github-driven-workflow` §8)

- **Broker route** (when `REVIEW_ACQUIRE_SCRIPT` is set): `python3 "$REVIEW_ACQUIRE_SCRIPT"
  <owner>/<repo> <PR> <kind>` verbatim — never copy, relocate, unset or self-point it. Kind
  order from dot’s available review configuration (`codex` is the default; `copilot` while its allowance
  lasts). A cooldown between requests on one PR is not an error. A
  `chatgpt-codex-connector[bot]` reply telling you to create a Codex account is a canned
  response to an unauthorised mention, not a failure: keep waiting for the real review.
- **Bundled route**: `github-driven-workflow`'s `scripts/acquire-review.py` when no broker.
- **Reviewed-by route** (no bot reviewer available, affirmative broker failure, a judge the
  governing Issue mandates, or any push that invalidates final-head evidence once the
  five-request ceiling is reached): a read-only
  reviewer distinct from the implementer (different model or session) posts a PR comment
  beginning `Reviewed-by: <reviewer-id>` that states its findings and the head SHA it covered.
  It is comment-based evidence under §7 and carries the same weight as a formal Review event.
  Independence is by recorded identity. A bot review (formal Review event in any state, or a
  `Codex Review:` top-level comment) is evidence as it stands; do not re-post it as a
  `Reviewed-by:` artifact.

Wait for the review; minutes are normal. Poll without filtering by review state or author
login — codex delivers formal reviews as `COMMENTED`; a top-level `Codex Review:` comment
counts as it stands when it or the bot's review-summary comment names the reviewed commit and
that commit is the current head, otherwise obtain review of the current head; the owner may
review in any form. Change route only on affirmative evidence
that this one will not deliver (explicit error, quota-exhausted body), never on elapsed time.
A connector reply that the Codex usage limit for code reviews is reached is such evidence:
run the read-only `codex exec` (or subagent) review on the PR head and post it as the
`Reviewed-by:` artifact.

## Observation, disposition and merge

One policy for the driver and the orchestrator; The continuing loop, the orchestrator tick and the dispatch
prompt refer here.

```markdown
Observe current review bodies, comments and threads without filters that
hide relevant interventions. Apply github-driven-workflow's evidence,
feedback-disposition and existing-authority checks before merge. Handle
ordinary corrections autonomously; owner participation alone creates no
checkpoint. Pause only actions dependent on an actual blocking condition.
```

- A returned review proves acquisition, not disposition; a negative review is evidence that
  review happened, and its findings still need a disposition.
- Owner comments and correction pushes are ordinary input: integrate, validate and review them
  like any other change. An addressed ordinary change request proceeds under the existing
  merge authority without a new owner verdict.
- A reservation — stated in the governing Issue or explicit instruction, or a clear owner
  statement on the Issue or PR such as "review still underway" or "wait for my decision on X",
  no keyword required — holds until an authorised amendment removes or satisfies it. Owner
  activity alone is not a reservation. A correction push, a report, or a request for re-review does not satisfy it.
  Pause the dependent merge; continue other authorised work.
- Record dispositions where the feedback lives: a thread reply, a linked fix or one grouped PR
  comment. No separate ledger. Explain a non-action only when it affects acceptance.
- Do not require `reviewDecision == APPROVED` and do not treat an absent optional signal as a
  blocker. Merge with `gh pr merge <N> --squash --match-head-commit <evaluated head>` for develop,
  or `--merge` instead of `--squash` for stable main promotions (ADR 0002)
  after refreshing the head and the latest interventions.

## Classification after every round

A finding is **substantive** (blocking) if acting on it would change a Lean statement, the
validity of a proof step, the axiom footprint, the behaviour of a guard or CI, or the
correspondence between the Lean development and the source. Severity follows the established
mathematical defect or contract violation (§ Contract-aware comparison), not the mere absence
of a written hypothesis. Wording, naming, comment style,
preference and restatement of something already correct are not, however confidently argued.

- Substantive → fix, push, record the disposition, and re-request review of the new head
  through the applicable PR review route above. No additional reviewer is dispatched for this
  beyond that route.
- Non-substantive → no further round for it. The orchestrator files a hygiene Issue for anything
  worth keeping.
- Any push after review, substantive or not (including a wording fix, rebase or conflict
  resolution), invalidates the evidence for the changed head: re-request review of the final
  head through the applicable route before merge. Evidence on a stale head never covers later
  changes.

**Five rounds is the ceiling for new automatic review requests on one PR.** Same defect shape
three rounds running → change the structure, not the instance. The ceiling limits rounds; it
does not dispose of a blocking finding, pass a failing gate or satisfy a reserved decision, and
neither does a clean result from another reviewer. A blocking finding raised at the ceiling is
fixed and its changed content reviewed by the next available route (for example the read-only
`Reviewed-by:` route); if blocking findings keep arriving, stop the merge and report a
Specification or Technical blocker with the evidence. Non-blocking remainder goes into one
follow-up Issue.

## Judge records

A judge review runs only when the governing Issue requires one for a PR; it is not a
routine round and is never added after the broker review as a parent approval step. Its verdict is an ordinary review record under the
reviewer-identity contract above (a `Reviewed-by:` comment on the PR) — no second
`Judged-by` format, no duplicate judge and review posts, no separate status ledger, and no
per-theorem table required for formatting. It states the reviewed
revision (commit SHA) and the comparison mode actually used: `source-based` (the primary source
was read) or `digest-based` (compared against something other than the primary source — the
`docs/math/` digest, a secondary source or the owner's brief — named in the record). These are
the only two modes; partial coverage is a qualifier stated with either. Its
body or links identify the target, the source or digest compared, and the verdict. The mode
describes the evidence; it does not waive a source comparison the Issue requires.
A `digest-based` verdict never closes a required primary-source comparison: that stays
tracked as outstanding work (the source-fidelity policy of `loop-orchestration-scaffold`).

## Statement-changing PRs

Any PR that adds or changes a public statement carries a short source ↔ Lean correspondence
section in its body, and its reviewer checks literal Lean vs source, hidden assumptions,
boundary cases and quantifier/domain mistakes. The broker review covers this by default;
the governing Issue may additionally require a judge (reasoning tier, read-only,
`lean-formalization-discipline`, `math-semantic-preservation`) for results whose source
comparison is contested or release-scoped, stated in the contract before dispatch. Every such review applies the next section.

## Contract-aware comparison

```markdown
Compare the complete statements, inherited assumptions and specialisation
map before classifying an omitted source hypothesis. A proved result that
entails the requested source result is not a mathematical weakening.
Do not infer strict generalisation or equivalence merely from a shorter
hypothesis list or an unused proof argument.

Check the deliverable contract separately. Preserve a required exact
public name and type, or the expressly requested source-form statement,
even when a stronger supporting theorem is available. When no exact
interface is required, do not manufacture a mandatory specialisation
corollary merely to reproduce unused hypotheses.
```

Two separate questions, answered in the review record:

- **Mathematics.** Which relationship is established: equivalent, the source result as a
  checked specialisation of the Lean result, or weaker? Distinguish removal of a genuinely
  redundant assumption from extension to additional cases; a proof not using an assumption is
  not evidence that it follows from the others. Claim strictness only where it is established.
  A changed assumed interface or structure field is checked for its actual consequences, not
  treated as a proved strengthening.
- **Contract.** What does the governing Issue require: a proof of the source result, the
  source-form statement, or a frozen public name and type? A stronger supporting theorem may
  coexist with the required public result. If the contract requires the source statement,
  supply its checked specialisation; if it also freezes the name and type, keep that entry
  point — an unrelated new alias does not satisfy it. Do not add unused hypotheses to every
  result, and do not silently replace a frozen interface.

Severity follows the established defect or violation. A legitimate strengthening within the
contract does not block; an exact-interface mismatch can block delivery even when the Lean
result implies the source. Never assign ADVISORY solely because a theorem is proved or a
written hypothesis is absent. State the relationship succinctly where readers or callers need
it (docstring, correspondence section).

## Source beats digest

Compare against the directly available authoritative source (fetch the arXiv/DOI text) rather
than defaulting to the digest; a reviewer's "the paper says X" is checked against the paper
before ruling. Digests have been wrong in exactly this shape before. A citation or a digest
does not establish that the primary source was read: record the comparison mode actually used
(§ Judge records).
