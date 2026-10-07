# Orchestration guide (minimal)

How a repository created from this template runs itself. Everything longer lives in the
skills under `.claude/skills/`; this page is the map.

## Roles

Five abstract roles. Any vendor harness that can run a session, spawn a subagent and call
`gh` can fill each one; the mapping is configuration, never code (ADR 0001).

| Role | Owns | Never does |
|---|---|---|
| **Orchestrator** | the loop: observe GitHub, select one `agent:ready` Issue, rule the design on the Issue, dispatch a driver, adjudicate escalations, merge when the driver cannot, file follow-up Issues, run the periodic tick | implement, take over a driver's PR, poll a busy driver |
| **Driver** | one Issue end to end under `github-driven-workflow`: worktree, worker dispatch, the compile loop (`scripts/check.sh`), local review, PR, review acquisition, fixups, merge, cleanup | author the deliverable itself when a worker route is available; end a turn waiting on background work |
| **Worker** | one bounded implementation block (≲ 400 Lean lines) or research unit, written to the driver's worktree | run the Lean toolchain (the driver compiles and feeds back exact errors) |
| **Reviewer** | independent review evidence on the PR (`github-driven-workflow` §7/§8) | edit the branch |
| **Judge** | one bounded read-only judgement: source ↔ Lean fidelity, statement-weakening audit, terminology | implement or review diffs at large |

## Model tiers

The skills never name a vendor model. They name one of two **tiers**, and the generated
container contract resolves each tier to a concrete model for the vendor(s) in use:

| Tier | Used for | Claude Code | Codex |
|---|---|---|---|
| **routine** | drivers, workers, mechanical edits, fix rounds, API sweeps, drafting | Sonnet | `gpt-5.6-luna` at `xhigh` |
| **reasoning** | orchestrator rulings, hard first drafts, statement design, exposition, review judgement, judges | Opus (Fable where available) | `gpt-5.6-sol` at `high` |

Defaults: the driver is routine tier (a routine driver with a ruled design outperforms an
unruled reasoning driver, and it never hits the weekly cap that has killed reasoning-tier
drivers); the judge is reasoning tier; the worker is routine tier except for the first draft
of a genuinely hard block. Pick the reasoning tier deliberately, per task, when latency or
writing quality is the binding constraint, and record the reason on the Issue. A dispatch
names the resolved model; the mapping above is the only place vendor names appear.

Vendor mapping of the roles:

| Role | Claude Code | Codex |
|---|---|---|
| Orchestrator | interactive `claude` session (reasoning tier); tick via `/loop 1h` or cron `claude -p` | `codex` session (reasoning tier); tick via cron `codex exec` |
| Driver | `Agent` subagent, **model named explicitly** (routine tier by default; reasoning tier when the Lean statement design or exposition quality is the deliverable) | `codex exec` in the worktree, or a Codex subagent (same tier rule) |
| Worker | codex plugin `codex-companion.mjs task --write` (routine tier; reasoning tier for a hard first draft) or `Agent` subagent (routine tier) | `codex exec --full-auto` in the worktree (routine tier) |
| Reviewer | `$REVIEW_ACQUIRE_SCRIPT` broker (`codex` / `copilot`); fallback: read-only subagent posting a `Reviewed-by:` comment | `$REVIEW_ACQUIRE_SCRIPT` broker (`codex`), else `github-driven-workflow`'s bundled `acquire-review.py`; fallback: read-only `codex exec` posting a `Reviewed-by:` comment |
| Judge | read-only `Agent` (reasoning tier) with 3–4 skills and one responsibility | `codex exec` read-only (reasoning tier) |

## Two configurations

**A — long-running multi-agent loop** (the `mobius-cpt` configuration; default when more than
one subscription is available). Orchestrator on Claude (reasoning tier), routine-tier driver,
codex worker, broker reviewer, reasoning-tier judge. Event-driven: the orchestrator wakes on a
driver report
or an escalation; a periodic tick (~1 h) is the backstop, never the main loop. One driver at a
time. The scarce resources are the Claude quota and container memory, in that order — move
work to the worker/reviewer routes wherever they can take it.

**B — single subscription.** The orchestrator and driver collapse into one session that runs
Issues sequentially; roles still stay separate *per Issue* through subagents:

- *Claude only*: driver = routine-tier `Agent` subagent that writes the blocks itself (an
  `Agent` subagent cannot spawn subagents, so there is no worker below it); when the Issue's
  head is gate-green and meets the Issue's acceptance criteria (a contract Issue lands with
  its authorised holes) it pushes, reports and ends its turn (one checkpoint per Issue); the
  orchestrator dispatches the judge and the read-only local reviewer (reasoning tier, a
  different model than the driver), rules on the Issue, and resumes the driver by
  `SendMessage` for fixes, the PR, the review round and the merge; PR reviewer = the broker
  when `REVIEW_ACQUIRE_SCRIPT` is set, else the orchestrator reruns the read-only reviewer
  on the PR head once the PR is open and posts its `Reviewed-by: claude-<model>-reviewer`
  comment quoting that head (comment-based evidence under §7); judge = reasoning-tier subagent. A subagent dies
  at the session-limit boundary; re-dispatch it under a new name (a driver's branch is the
  durable state).
- *Codex only*: driver = the session; worker = `codex exec` per block (routine tier);
  local reviewer = a fresh read-only `codex exec` at the reasoning tier with the numbered
  risks on stdin (`codex review` has no `-m` flag and rejects a prompt next to `--base`, and
  its default sandbox writes); PR reviewer = the broker when `REVIEW_ACQUIRE_SCRIPT` is set,
  else `github-driven-workflow`'s bundled `acquire-review.py`, else that read-only
  `codex exec` recorded as
  `Reviewed-by: codex-cli-<model>-<session id>` (the session id is what makes a same-model
  review independent of the implementer); judge = a fresh `codex exec` at the reasoning tier with
  the fidelity prompt. The Codex CLI does not stop at 100 % of its window: it spends the
  prepaid credit balance next. A run that must not pay as it goes starts with a zero balance;
  checking `codex_window` (`scripts/preflight.sh`) before every `codex exec` narrows the
  spill but cannot prevent it.

Both configurations use the same Issue/PR gates, the same scripts and the same skills; only
the vendor mapping differs, and it is recorded in the generated container contract
`.claude/skills/<project>-orchestration/SKILL.md`.

## Lifecycle

```
initial prompt ─▶ Init (preflight, charter, self-rewrite) ─▶ Decompose ─▶ Loop ─▶ Submit
                                                   └─(opt-in, after M1)─▶ Exposition lane
```

1. **Init** — `scripts/preflight.sh`, `scripts/bootstrap.sh`, `scripts/github-setup.sh`; the
   charter Issue; `scripts/rename-project.sh`; digest of the sources into `docs/math/`;
   rewrite of `AGENTS.md`; generation of the container contract; ADR 0002 kept or escalated.
   Ends with the first PR through `github-driven-workflow`, which doubles as a dry run of the
   review route.
2. **Decompose** — `lean-issue-decomposition`: statement-contract Issue first, then
   source-anchored block Issues with dependencies drawn on the charter; `agent:ready` only after
   an audit by an agent distinct from the eventual implementer.
3. **Loop** — `github-loop-engineering` outside, `github-driven-workflow` inside, review order
   from `lean-review-routing`. Every dispatch prompt is instantiated from
   `.claude/skills/loop-orchestration-scaffold/references/dispatch-prompt.md`.
4. **Submit** — final gate, fidelity judgement of the main theorem(s) against the source
   (final, provisional or fails as defined in `loop-orchestration-scaffold` Phase 6 step 2),
   README results section, charter closure comment, tag; archival (Zenodo, `CITATION.cff`) is
   an owner decision.
5. **Exposition lane** (optional; opt-in through the initial prompt or a later explicit
   writing request) — kickoff settles the reader brief in a note Issue; after the target
   statements are frozen a writer drafts `docs/note/` against a pinned formalisation revision,
   in parallel with the Lean lane; reviewers chosen from the actual changes get the same brief;
   `scripts/check-note.sh` (inactive until `docs/note/note.conf` exists) builds and checks it
   locally and in CI; delivery is the merged source and the CI-built PDF, extras on request
   (`loop-orchestration-scaffold` § Exposition lane).

## Entry

Create the repository from the template, clone it, open the harness in the clone, and paste
the initial prompt (template:
`.claude/skills/loop-orchestration-scaffold/references/initial-prompt.md`). `AGENTS.md` /
`CLAUDE.md` route the first session into the Init phase; nothing else is required.

Periodic backstop, once the loop runs:

```sh
# Claude Code, inside the orchestrator session:
/loop 1h "$(cat .claude/skills/loop-orchestration-scaffold/references/orchestrator-tick.md)"
# or from cron (either vendor):
claude -p "$(cat .claude/skills/loop-orchestration-scaffold/references/orchestrator-tick.md)"
codex exec "$(cat .claude/skills/loop-orchestration-scaffold/references/orchestrator-tick.md)"
```

## Prerequisites

Skills the loop assumes: `github-driven-workflow`, `github-loop-engineering`,
`lean-formalization-discipline` (source: <https://github.com/t-uda/skills>). Each harness
has its own discovery path — Claude Code reads `.claude/skills/` and `~/.claude/skills/`,
Codex reads `.agents/skills/` and `~/.agents/skills/` — so install them at user level for
the vendor(s) in use, or vendor them into the repository under both paths. The bundled
skills are tracked under both (`.agents/skills/<name>` is a relative symlink to
`.claude/skills/<name>`); `scripts/preflight.sh` reports every prerequisite per vendor.
Without them the Init phase stops with a Technical blocker naming the missing skill; it does
not improvise a replacement. `gh` authenticated as the maintainer account; elan; a mathlib
olean cache reachable by `lake exe cache get` or by hardlink from a sibling checkout.

## Hard rules

- No direct pushes to `main`; every change is Issue → branch → PR → review → `check` → squash.
- No status/progress/plan documents in the tree; scratch goes to `.claude/scratch/`.
- Every subagent dispatch names its model.
- Every Lean invocation holds `/tmp/lean-build.lock` (enforced by `.claude/hooks/lean-guard.sh`).
- Owner decisions only for: destructive actions, money, a fatal mathematical gap, or
  something only the owner can do — recorded on the Issue (`needs-decision`). Everything else
  is decided and recorded on the Issue.
- No unsolicited notifications: only a genuine emergency, or a delivery the owner explicitly
  requested (`loop-orchestration-scaffold` § standing rules).
- Review feedback is observed unfiltered and disposed of under one policy
  (`lean-review-routing` § Observation, disposition and merge); owner participation alone is
  not a checkpoint.
- Processes are stopped only by ownership (launch tag `LOOP_JOB_ID`) and absence of live
  work, never by path (`.claude/hooks/codex-chains.sh`).
