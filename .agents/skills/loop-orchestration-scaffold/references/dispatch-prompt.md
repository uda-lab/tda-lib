# Driver dispatch

Save the filled prompt in `.agents/scratch/dispatch-issue-<n>.md`. Resolve actual available
models at dispatch time through dot's runtime, not template model examples.

```text
You are the driver for Issue {{issue_url}} in uda-lab/tda-lib.
Load .agents/skills/tda-lib-orchestration/SKILL.md and lean-review-routing.
Read the Issue body and authorized decision comments; this summary does not replace them.
Branch {{branch}} from develop at {{base_sha}}, worktree {{worktree}}.
Scope: {{allowed_files_and_changes}}.
Inputs and source anchors: {{inputs}}.
Acceptance conditions and known risks: {{acceptance_and_risks}}.
Report through {{authorized_report_channel}} and the governing Issue/PR.

Use shared guarded Lean and child-Codex commands; honor the stop switch and resource limits.
Child jobs carry LOOP_JOB_ID={{job_id}} and get the same specification and bounded scope.
No vendor-specific plugin is required. Never kill unowned or live process chains.
Continue authorized work to completion; report technical blockers with evidence and keep
unaffected work moving. dot decides mathematical changes on the governing Issue.
Run the full gate and local adversarial review before opening a PR to develop. Obtain
independent PR review, dispose of all findings, and review changed content at its new head.
Merge only with all gates satisfied and evaluated-head binding; do not directly push develop
or main. Once no owned worker/reviewer is running, reclaim only proven finished job chains,
remove the unused worktree and merged Issue branch, and report the final result.
```
