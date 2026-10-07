Orchestrator tick for this repository. Load `.claude/skills/<project>-orchestration/SKILL.md`,
`loop-orchestration-scaffold`, `github-loop-engineering`. Do exactly one Observe → Select →
Act cycle from current GitHub state; do not implement anything yourself.

1. Observe: open PRs (gates; every review body, comment and thread with no author or state
   filter; the reviewed head against the current head), Issues with `agent:ready` and no PR
   (body plus authorised decision comments), hard-stop labels, new comments addressed to you,
   the driver registry in `.claude/scratch/drivers.md` if one exists.
2. For each in-flight PR, apply `lean-review-routing` § Observation, disposition and merge:
   merge-ready and idle → merge per ADR 0002
   (`gh pr merge <N> --squash --match-head-commit <evaluated head>`) only if its driver is
   gone; otherwise re-engage the driver once with the exact condition. Owner participation
   alone is not a hold; a reservation stated on the Issue is, for the merge only. Stalled (no push, no comment, no build > 60 min) → read the driver
   transcript tail, re-engage once or stop-and-redispatch on the same branch.
3. If no Issue is in flight and an authorised, unblocked Issue exists: rule the design on the
   Issue, dispatch one driver from `references/dispatch-prompt.md` with a named model.
4. If nothing is executable: report why in the no-fake-blocker structure and stop. Do not
   manufacture work; do not poll. The report is the tick's output, not a notification: send
   nothing to the owner unless the notification rule allows it.
5. Update the container contract if a measured fact changed (through a PR, not scratch).
6. Codex chains of this repository's finished jobs are reaped by the SessionStart hook; for a
   driver known to be gone, `. .claude/hooks/codex-chains.sh; reap_codex_chains '<its LOOP_JOB_ID>'`
   (run without `LOOP_JOB_ID` set; never by path).

End with: Done / Gate state / Next automatic action / Blocker (if any, with category).
