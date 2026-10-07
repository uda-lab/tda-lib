# Container contract template

Generated in Init Phase 3 as `.claude/skills/<project>-orchestration/SKILL.md` (tracked —
it is policy). Replace every `{{…}}` with a measured or decided value; delete rows that do
not apply to the chosen configuration. Keep it under ~150 lines; move anything longer into
`docs/orchestration.md` or an ADR.

```markdown
---
name: {{project}}-orchestration
description: Container contract for the {{owner}}/{{repo}} formalisation loop — tiers, vendor mapping, fan-out caps, exact worker/reviewer invocations, memory rules, kill switch, escalation boundary. Load first in every orchestrator session on this repository.
---

# {{project}} orchestration (this container)

Companion to `loop-orchestration-scaffold` (procedure), `github-loop-engineering` (outer
loop) and `github-driven-workflow` (per-PR gate). Only what is specific to **this
repository and this machine**, measured on {{date}}.

## Repository facts
- Repo `{{owner}}/{{repo}}`, default branch `main`, ruleset: {{ruleset_summary}}.
- Identity `{{gh_login}}`, permissions `{{permissions}}`. Owner-only actions (escalate, never
  attempt): visibility, rulesets, secrets, mathlib pin, budget.
- Merge authority: {{ADR 0002 granted | needs-decision #n}}. Merge command:
  `gh pr merge <N> --squash --match-head-commit <evaluated head>`.
- Reserved owner decisions: {{none | as listed on the charter}}.
- Charter Issue #{{charter}}; mathematical SoT `docs/math/{{digest}}.md`.

## Configuration {{A | B-claude | B-codex}}

Model tiers resolved for this repository (`docs/orchestration.md` § Model tiers is the source):

| tier | resolved model / effort | vendor |
|---|---|---|
| routine | {{e.g. Sonnet | gpt-5.6-luna xhigh}} | {{Claude | Codex}} |
| reasoning | {{e.g. Opus | gpt-5.6-sol high}} | {{Claude | Codex}} |

| role | who | tier | notes |
|---|---|---|---|
| orchestrator | {{harness}} | reasoning | event-driven; tick ~1 h backstop |
| driver | {{Agent subagent | codex exec}} | routine (reasoning only with the reason on the Issue) | one per Issue, disposable (B-claude only: writes the blocks itself and checkpoints once, on the head that meets the Issue's acceptance criteria) |
| worker | {{codex plugin | Agent | codex exec}} | routine; reasoning for a hard first draft | foreground, ≤ 400 Lean lines/job |
| reviewer (PR) | {{broker kind | Reviewed-by route}} | — | `{{pr_review_invocation}}` |
| reviewer (local) | {{codex adversarial-review | read-only codex exec | read-only subagent}} | reasoning | numbered falsifiable risks |
| judge | read-only {{Agent | codex exec}} | reasoning | 3–4 skills, one responsibility |

Fan-out caps: one driver per lane, {{lanes}} lane(s); no fleets, no parallel review panels.

## Exact invocations
- Worker: `LOOP_JOB_ID=<Library>/issue-<n>/<role> {{worker_invocation}}` (cwd = worktree;
  foreground). The job's leftover chains are reaped once it ends with
  `. .claude/hooks/codex-chains.sh; reap_codex_chains '<LOOP_JOB_ID>'` — never by path.
- Local review: `{{local_review_invocation}}`. For Codex the measured form is
  `codex exec -C <worktree> --sandbox read-only -m <reasoning model> -c model_reasoning_effort='"high"' - < <worktree>/.claude/scratch/local-review-issue-<n>.md`
  (never `codex review`: no `-m` flag, and no prompt next to `--base`).
- PR review: `{{pr_review_invocation}}` — invoke `$REVIEW_ACQUIRE_SCRIPT` verbatim when set;
  cooldown {{cooldown}} s between requests on one PR is not an error.
- Kill switch: `echo "<reason>" > /tmp/codex-stop` (enforced by `.claude/hooks/lean-guard.sh`);
  `rm /tmp/codex-stop` lifts it.

## Machine limits (measured)
- Memory cap {{cgroup}}; swap {{swap}}; `LEAN_GUARD_MIN_AVAIL_MIB={{min_avail}}`,
  `LEAN_NUM_THREADS={{threads}}` (in `.claude/settings.local.json`). `exit 137` = OOM; confirm in
  `/sys/fs/cgroup/memory.events`.
- Package oleans shared from `{{sharable_packages}}` by `cp -al`; never hardlink `.lake/build`;
  never cold-build mathlib.
- Worktrees under `{{worktree_root}}/<slug>`; install the guard there with
  `bash .claude/hooks/install.sh <path>` if the harness does not read `.claude/settings.json`
  from the worktree.

## Quotas
{{Claude plan and reset; codex window and reset; review credits; pay-as-you-go: never}}
A Claude subagent dies at the session-limit boundary with "You've hit your session limit";
re-dispatch it under a new name once the window resets (a driver's branch is the durable
state; a judge or reviewer is simply rerun).
Codex does not stop at 100 % of its window: the CLI continues on the prepaid credit balance
until that is 0. "No pay-as-you-go" holds only with a zero balance (owner action; balance
{{codex_credits}} at Init). A `codex_window` check (`scripts/preflight.sh`) before every
`codex exec` narrows the spill window but cannot close it, since the window can cross 100 %
mid-request; a `codex_window_stale: yes` reading is no evidence either way.

## Owner decisions and notifications
Owner-only decisions — destructive/irreversible action, financial commitment, fatal
mathematical error or gap, owner-only action — go on the Issue or charter (`needs-decision`),
pausing only the dependent action. Everything else is decided and recorded on the Issue.
Notifications follow `loop-orchestration-scaffold`'s rule: none unsolicited except a genuine
emergency, once, on {{emergency_channel}}; explicitly requested deliveries:
{{requested_deliveries | none}}, within their scope. A reviewer quota observed exhausted
and the route change are recorded on the PR, not sent.

## Dispatch-prompt checklist
`references/dispatch-prompt.md` of `loop-orchestration-scaffold`, every placeholder filled,
plus these repository traps: {{traps learned so far — update this list from PRs}}.
```
