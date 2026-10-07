# docs/math — mathematical source of truth

This directory holds the **working digest** of the source papers and nothing else: exact
statements to be formalised, the conventions the Lean development commits to, and the
bibliography. It is written during the Init phase (see
`.claude/skills/loop-orchestration-scaffold/SKILL.md`) from the papers named in the initial
prompt, and amended only through PRs that cite the source.

- `references.md` — every primary source with a stable identifier (DOI, arXiv id) and the
  short key used in Issues and docstrings (`[T26]`, `[CRTT25]`, …). The papers themselves
  are **not** tracked; keep local copies under `sources/` (gitignored).
- `<digest>.md` — one file per programme: definitions, the target theorem(s) verbatim in the
  source's vocabulary, the dependency route (lemma chain), and every convention choice the
  Lean encoding makes (sign, normalisation, quantifier order, domain).

The primary papers win on any conflict with a digest. A digest is not a status document: it
records what the mathematics *is*, never which Issue landed what — that lives in Issues, PRs
and Git history.
