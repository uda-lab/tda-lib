# Initial prompt (owner → first session)

Paste this, filled in, as the first message in the harness opened inside the fresh clone.
Fields marked (required) block the corresponding Init step until answered; everything else
has the stated default.

```
You are the orchestrator of this repository (created from lean-formalization-scaffold).
Load .claude/skills/loop-orchestration-scaffold/SKILL.md and run it from Phase 0.

Project name / Lean library name (required): <Name>            # e.g. MobiusCPT
Sources (required): <list: title, authors, DOI or arXiv id, local path under sources/ if any>
Source fidelity: <what the deliverable is checked against>      # default: the primary sources
                                                                # (outcomes: loop-orchestration-scaffold Phase 6)
Target (required): <the theorem(s) to formalise, cited by number in the source; the
                   definition of done in one sentence>
Non-goals: <what is explicitly out of scope>                    # default: nothing beyond the target
Configuration: A | B-claude | B-codex                           # default: A if more than one
                                                                # subscription is available
Owner GitHub login (required): <login>
Trusted AI maintainer login: <login>                            # default: the gh account in use
Merge authority: granted per docs/adr/0002 | not granted        # default: not granted → needs-decision
Reserved decisions: <owner approvals required before specific merges, or none>  # default: none
Emergency channel: <Discord channel id | GitHub Issue | none>   # default: the charter Issue; used only
                                                                # for a genuine emergency, never for progress
Requested deliveries: <explicit messages you want, e.g. "completion report to <channel>">
                                                                # default: none — no unsolicited notifications
Quotas / budget: <Claude plan, codex window, review credits, pay-as-you-go allowed? (default: no)>
Exposition: <none | a reader-facing note: for whom, to learn or decide what, language>
                                                                # default: none; can be requested later
Deadline: <date or none>
Container: <memory cap, sharable mathlib checkout path, anything preflight cannot measure>
```
