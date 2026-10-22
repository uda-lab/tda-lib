# Continuing coordination tick

Load `.agents/skills/tda-lib-orchestration/SKILL.md` and the continuing loop skill.
Read GitHub Issues, ready labels, open PRs, current heads, CI and review comments.
Resume active work before dispatching new work; enforce one driver per lane and exclusion for shared mutable build/dependency
paths. Coordinate independent builds for available resources. dot rules on scope and roadmap decisions on the governing Issue.
Give each driver the complete Issue and decision comments using `dispatch-prompt.md`.
Use shared guarded commands; honor `/tmp/codex-stop`. Reclaim only finished owned jobs through
`scripts/agent/codex-chains.sh`; report live or untagged processes without killing them.
Drivers resolve review findings and merge their own qualifying PRs with evaluated-head
binding; re-engage a stalled driver, and merge in its place only when it cannot (ADR 0002).
Remove merged Issue branches and unused worktrees, never develop. Promote and tag stable
releases only when their gates hold. Resume from GitHub on the next externally scheduled
invocation.
