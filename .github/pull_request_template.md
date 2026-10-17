Closes #

## Summary

## Branch lifecycle
<!-- State the target scope/milestone and release version ("undecided" is valid before release cut).
Identify the branch role, source/base, destination and method: ordinary code/docs topics are
develop → develop squash PRs; release/hotfix propagation uses merge-commit PRs. Keep develop/main.
For release/hotfix or main-first documentation fixes, link every required propagation destination
and its remaining work, including eventual develop integration through an active release. Record
the actual reviewed fixing/release head and separate ancestry from content-preservation checks;
retain later correct develop additions. Ordinary topic PRs may write "Propagation: N/A".
See CONTRIBUTING.md. Do not add empty task boxes or a routine develop-refresh/approval gate. -->

## Public declarations added / changed

## Source ↔ Lean correspondence
<!-- Required for statement-changing PRs: for each new or changed public statement cite the source
(paper, theorem/equation number, or docs/math/<digest>.md §) and state every deviation
(conventions, domains, quantifiers). For an omitted source hypothesis state the established
relationship (equivalent / source result as checked specialisation / weaker) and, separately,
whether a required exact public name and type is preserved. Otherwise write
"N/A — no statement change". -->

## Validation
<!-- Record evaluated head/base SHAs, exact local commands and outcomes, applicable audit/coverage
results, and the hosted CI run for this head. Require the existing workflow's `check` to succeed;
local success does not replace it. For prose-only changes, report focused checks and the workflow's
conditional build skip honestly. Keep existing docs/note conditions; do not add CI-skip markers
to suppress routine validation or run full doc generation merely for this section. -->

## Remaining sorry / custom-axiom footprint
<!-- "none", or each ALLOW_SORRY / ALLOW_AXIOM marker with its authorising Issue. -->

## Independent review evidence
<!-- Reviewer identity distinct from the implementer, with a link. For statement-changing PRs the review
must cover: literal Lean vs source; proof integrity and hidden assumptions; adversarial boundary cases and
quantifier/domain mistakes; unnecessary bookkeeping or transient artefacts. -->
