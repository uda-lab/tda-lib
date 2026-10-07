# Exposition dispatch (writer and reviewers)

The exposition counterpart of `references/dispatch-prompt.md`. Its specification-intake,
turn-discipline, report, notification, review-observation, merge and cleanup clauses apply
unchanged; this file adds what a writer and its reviewers need. Save the filled prompt to
`.agents/scratch/dispatch-note-{{n}}.md`; name the model (resolved by dot’s runtime —
exposition quality is a reasoning-tier reason, recorded on the Issue). Allocation follows the
existing capability and resource policy: no fixed vendor, and no agent per skill.

Both prompts start with the same shared context, filled once; the writer and every reviewer
receive it verbatim.

```
## Shared context (writer and every reviewer)
Note Issue #{{n}} in {{owner}}/{{repo}}: {{issue_url}}.
Read the issue body and relevant authorised decision comments before
acting; a dispatch summary does not replace the agreed specification.
Distinguish settled amendments from proposals and pass the same governing
context to implementation and review.
The agreed brief and audience model are the Issue's § Brief, settled under:
  Read the request, source context and authorised issue decisions, including
  relevant comments, before asking questions. Clarify what the readers need
  to learn or decide, what they already know, and what content or depth is
  excluded. Ask only about consequential unresolved choices. Record the
  agreed brief in the exposition issue, distinguishing assumptions and open
  questions; carry later explicit corrections into drafting and review.

For reader-facing deliverables, use exposition-flow after requirements
are clarified. Give drafting and review agents the agreed brief and
audience model, or an accessible reference to them, rather than only
an audience label.

Identify the formalisation revision the note reports. Unrelated changes
to main do not require updating a deliberately versioned report. When
its target revision changes, reassess all affected claims, proof
explanations, findings, limitations and source correspondences, not only
an appendix. Do not ignore a known defect affecting the reported result
merely because the report pins an older revision.
Reported revision: {{revision}}. Source fidelity: {{fidelity}} (provisional stays labelled).

Select review skills from the actual changes and their affected
invariants, not merely the task label. A stylistic or structural edit
may require mathematical review. Give reviewers the relevant diff,
source context and agreed brief. Reassess coverage when later edits
affect content that an earlier review cleared.
```

Writer prompt — the shared context, then:

```
You are the writer, on {{model}}. Reports go only via {{report_channel}}.

## Scope
Edit only docs/note/ {{peripheral_edits}}. Never the mathematical source, frozen public
statements, docs/math/ or unrelated infrastructure. Report a mathematical defect you find via
{{report_channel}} (the orchestrator files it), and state its effect in the note; never
conceal it.

## Build
`bash scripts/check-note.sh` must print PASSED on the head you hand over; NOT CONFIGURED or
NOT RUN is not a pass. `--text` writes the rendered text for the language pass.

## Review and merge
Obtain review per the shared context's selection rule; evidence, disposition and merge follow
`lean-review-routing` § Observation, disposition and merge.
```

Reviewer prompt — the shared context, then:

```
You are an independent reviewer, on {{model}}, read-only. Skills: {{skills chosen from the
changes}}. Review against the § Brief, not an audience label. Diff: {{diff or range}}.
Source context: {{Lean declarations and docs/math/ sections the changed text reports}}.
Rendered text (language pass): {{docs/note/build/<stem>.txt from check-note.sh --text, or
"unavailable"}}. Record the reviewed head SHA with your findings.
```

One independent reviewer may apply several relevant skills; a later language fix that touches
mathematical wording gets a scoped semantic recheck — ordering the language pass last is not
enough by itself. A Japanese language pass (`wabun-math-style` when present) gets the current
rendered text when available; visual inspection of the PDF is a separate responsibility. Use
released skills only, and name any dependency on an unreleased one on the Issue rather than
assuming it.
