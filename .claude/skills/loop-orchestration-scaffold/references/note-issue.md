# Note Issue template

Title: `[note] <what the readers get> for <audience>`. Label `infrastructure` only if the Issue
names peripheral edits (build, CI, bibliography, shared style); otherwise the default. Normal
authority: `agent:ready` after the usual scope/acceptance audit. The body is the specification;
edit it (not a comment thread) when the brief changes.

```markdown
## Brief
<Natural language: who the readers are; what they need to learn or decide; what they already
know (mathematics, the method, Lean); what is excluded or kept shallow; language and register;
target length and proof depth; notation source; authorship of the note and of the sources it
reports (verified, not inferred from handles); delivery route (the PR and its CI artifact,
plus anything the owner explicitly requested).>

Assumptions: <what was inferred from context rather than stated>
Open questions: <consequential choices still unresolved, or "none">

## Reported revision
Formalisation revision the note reports: <main SHA or tag>. Source fidelity: <inherited from the
charter; provisional if the judgement it reports is>.

## Scope
Edits: `docs/note/` (sources, `note.conf`, figures, bibliography)<, plus named peripheral edits
and why>. Not authorised by this Issue: mathematical source, frozen public statements,
`docs/math/` digests, unrelated infrastructure. Mathematical defects found while writing are
reported for separate Issues and their effect on the note is stated, not concealed.

## Acceptance
- The note serves the brief (reader-facing review against the brief, not an audience label).
- Review coverage selected from the actual changes (`references/exposition-dispatch.md`).
- `bash scripts/check-note.sh` prints `PASSED` on the final head (NOT CONFIGURED or NOT RUN
  is not acceptance); CI keeps the PDF as the run's artifact.
- Extras only if requested here: <translation | publication/archival | skill-feedback log | none>.
```
