# 0003 — Freeze the Comparator pilot contract

## Context

[Issue #855](https://github.com/uda-lab/tda-lib/issues/855) assesses a scoped pilot of Lean
4's built-in `lake comparator` as an additional, narrow check on top of the existing audited
correspondence between `docs/math/rips-sampling-confidence.md` (Fasy et al., Lemma 4) and this
repository's Lean statements. Comparator checks agreement between a frozen, already-reviewed
reference and a production solution; it does not itself establish fidelity to a source digest
— that is the separate, prior source ↔ Lean review (PR #766).

The owner's ruled design is recorded on Issue #855 ("Ruled design for the bounded pilot,
execution authorised by the owner"), after the scaffold contract
([lean-formalization-scaffold#40](https://github.com/uda-lab/lean-formalization-scaffold/issues/40),
merged as `de6fb66`) and the toolchain bump (#929, merged as `a5df95d`, Lean/mathlib v4.35.0).
This ADR records that ruling as current fact; the Issue history records the deliberation.

### Three independent questions

None of the following substitutes for another (precedent: `lean-formalization-scaffold` ADR
0003, `generalized-jetedmd` ADR 0004):

1. **Source fidelity.** Does `ComparatorChallenge/Reference.lean` correctly translate
   `docs/math/rips-sampling-confidence.md` (Fasy et al., Lemma 4)? Only an independent
   reviewer reading the digest establishes this, before relying on Comparator's verdict. The
   reference is authored from the digest and PR #766's review of the production statement —
   never regenerated from the candidate solution — and a reference change is itself a
   statement change needing the usual source ↔ Lean review by a reviewer other than the
   implementer.
2. **Proof construction and kernel checking.** Does
   `TDA.Probability.measure_missedCover_le_card_mul` actually hold, with no `sorry` and only
   the allowlisted axioms? `scripts/check.sh`'s existing steps (textual guards, lake build,
   live axiom audit, axiom-coverage guard) establish this — this theorem is already proved and
   pinned in `scripts/print_axioms/Probability.lean`, independently of whether its statement is
   faithful to any source.
3. **Comparator agreement.** Does the solution module, as built, still match the
   already-reviewed reference's statement and the permitted axiom set?
   `scripts/check-comparator.sh` (`lake comparator`) establishes only this. It never re-reads
   the digest and never establishes (1); it also does not establish (2) on its own (see the
   coverage map below).

## Decision

- **Target.** One theorem: `TDA.Probability.measure_missedCover_le_card_mul`
  (`TDA/Probability/SamplingCoverage.lean`), already proved and pinned in
  `scripts/print_axioms/Probability.lean`. No other theorem is part of this pilot; the
  finite-API semantic-regression candidates noted on the Issue (2026-11-13 comment) stay
  secondary and out of scope for this PR.
- **Reference.** The separate `ComparatorChallenge` library (`ComparatorChallenge/Reference.lean`,
  root `ComparatorChallenge.lean`, a second `[[lean_lib]]`, not in `defaultTargets`) imports
  mathlib only and restates, under the same fully qualified names and the same literal
  universe names (`u` for the sample space, `v` for the cover index type), the target's full
  statement closure: `TDA.Probability.missedCover`, `TDA.Probability.iidMeasure`, and the
  statement of `TDA.Probability.measure_missedCover_le_card_mul`. The reference proof is a
  single `sorry -- ALLOW_SORRY: #855`, never imported by production; Comparator judges the
  solution's proof, not the challenge's. `definition_names` stays `[]`: no definition is a
  declared hole.
- **Contract.** `comparator.json`: `challenge_module` `ComparatorChallenge.Reference`,
  `solution_module` `TDA.Probability.SamplingCoverage` (the leaf module, not the root
  aggregator `TDA`), `theorem_names` `["TDA.Probability.measure_missedCover_le_card_mul"]` (a
  pinned subset of the union of `scripts/print_axioms/*.lean`, not equal to the whole
  inventory), `definition_names: []`, `permitted_axioms`
  `["propext", "Classical.choice", "Quot.sound"]`. `scripts/check-comparator.sh` refuses a
  config that drifts from this.
- **Gate.** Measured wall time of the real contract on this container: a cold run 54.7s, an
  immediately repeated (warm) run 46.0s — both under the 60-second threshold set on the Issue,
  so `scripts/check-comparator.sh` is wired as the last step of `scripts/check.sh` and
  `comparator.json` is added to `scripts/hooks/pre-push`'s full-gate trigger pattern. Both
  runs spend most of their time inside Comparator's own bubblewrap sandbox replaying ~3,000
  Lake jobs against already-built oleans (the sandbox re-verifies on every invocation
  regardless of host-side caching), so "cold" and "repeated" differ only modestly here. Nothing
  skips the step once wired, and both a rejection (exit 1) and a could-not-start condition
  (exit 2) fail it. No `.github/workflows/` change is part of this pilot.
- **Private-constant and universe constraints (precedent: `generalized-jetedmd` ADR 0004).**
  Lean mangles a private declaration's name with its declaring module's path, so a production
  statement that embeds a private constant can never match a reference restated in a separate
  file, and Comparator also compares a named constant's own definition when it is referenced
  inside a compared statement, and compares universe level names literally. `missedCover` and
  `iidMeasure` are public with explicit universe variables `u`, `v`, so this pilot's target does
  not hit that failure mode; any future target added to this pilot needs its own check of its
  full statement and named-definition closure for private declarations before relying on
  Comparator's verdict.
- **Import boundary.** `scripts/check-comparator.sh` itself enforces, in both directions, that
  no production or auxiliary module imports `ComparatorChallenge` and that no
  `ComparatorChallenge` module imports any project-local module outside itself, using
  `scripts/lean-code-scan.awk`'s `mode=import`/`mode=imports` (added by this PR alongside the
  pre-existing `mode=sorry`/`mode=axiom`/`mode=root`); opening a block comment from code
  inserts a token separator in the code stream, so a comment cannot glue `import` to a module
  name and hide the dependency. This repository's lexer already unescapes `«Escaped.Name»`
  identifiers to an opaque `«x»` token for every mode (unlike the scaffold and jetedmd
  precedents, which lack this), but `mode=import`/`mode=imports` inherit that same opacity: a
  guillemet-escaped import name is not recognised as matching a plain dotted module name — a
  known, accepted limitation shared with the other two modes, not a regression.
- **srcDir.** `scripts/check-comparator.sh` decodes `lakefile.toml` with Python's standard
  `tomllib` and recursively checks every *decoded* key, at every nesting level, for the literal
  name `srcDir`, rather than text-matching the key — the precedent on
  `generalized-jetedmd` PR #277 is that three successive reviews defeated successive
  text-matching attempts (a bare key, a quoted key, a basic-string key with a Unicode escape
  whose raw bytes contain no literal `srcDir`). It also rejects outright if a `lakefile.lean`
  exists, since a Lean build config could set `srcDir` programmatically where no TOML scan
  would see it.
- **Guarded Lean entry point for a disposable fixture project.** `scripts/check-comparator.sh`
  now runs `lake comparator` through `scripts/lean.sh`, but
  `scripts/test-comparator-semantics.sh` builds and compares against a disposable fixture
  project under `$ROOT/.lake` (never the real repository tree), so it cannot go through
  `scripts/lean.sh` (which only accepts `$ROOT` or `$ROOT/docbuild` as the Lake project). It
  applies the same three guards directly instead: the `${CODEX_STOP_FILE:-/tmp/codex-stop}`
  stop switch, the `LEAN_NUM_THREADS` default, and the memory-headroom check
  (`scripts/lib/resources.sh`'s `lean_check_headroom`).
- **Stable-release sorry policy.** `scripts/check-no-sorry.sh --stable` (run for `main`/stable
  checks) ignores the `ALLOW_SORRY` marker everywhere, requiring every staging hole to be
  discharged before a stable release — a policy written before this permanent, by-design
  reference library existed. `ComparatorChallenge/Reference.lean`'s `sorry` is not a staging
  hole: it states no claim a release relies on (Comparator judges the solution's proof, never
  the challenge's), `ComparatorChallenge` is never a default build target, and it is never
  importable from `TDA` (enforced by `scripts/check-comparator.sh`). `--stable` therefore
  prunes `ComparatorChallenge/` from its scan instead of discharging that proof; default mode
  needs no such exclusion, since the `ALLOW_SORRY: #855` marker already covers it there. No
  other path is exempted, and `--stable` still rejects an unmarked `sorry` anywhere in `TDA/`.
- **Guard self-test fixtures.** `scripts/test-guards.sh`'s root-aggregator fixture helper
  (`fixture()`) and `scripts/claude-cloud-setup.sh`'s embedded `lakefile.toml` copy both model
  the full library layout; adding a second `[[lean_lib]]` here means both needed updating
  (`fixture()` now stubs a valid root for every declared library, not just the one under test)
  — otherwise `bash scripts/test-guards.sh` fails even though the Comparator contract itself
  is sound. Fixing the first exposed a latent `grep -q`-on-a-live-pipe/`pipefail` race in the
  renamed-project fixture test: once the guard has two libraries to report instead of one,
  `grep -q` can exit after matching the first "OK:" line while the guard process is still
  writing its second, and under `set -o pipefail` that SIGPIPE failed the whole pipeline even
  though the match was found; fixed by capturing the guard's output into a variable before
  grepping it.
- **Pinned-inventory scale.** `scripts/print_axioms/` is a directory of per-area files
  totalling several thousand `#print axioms` pins, not the single file the scaffold and
  jetedmd precedents assumed. `scripts/check-comparator.sh` reads the union of
  `scripts/print_axioms/*.lean` and passes it to `jq` via `--slurpfile` (a temporary file),
  never `--argjson` (a command-line argument): the pinned inventory is far larger than
  `ARG_MAX` tolerates as an argv string.
- **Agent-skill compatibility symlinks.** `.claude/skills/<name>` entries in this repository
  are real symlinks into `.agents/skills/<name>` (documentation only, never Lean sources); the
  wrapper's symlinked-source check excludes `.claude/skills` by path, the same way it already
  excludes `.claude/worktrees`/`.claude/scratch`/`.agents/worktrees`/`.agents/scratch`, rather
  than flagging every symlinked directory in the repository regardless of relevance.

## Coverage map

| Safeguard | Enforced by | Comparator overlap |
|---|---|---|
| No unmarked `sorry`/`admit` | `scripts/check-no-sorry.sh` (textual, whole tree) | Partial — for `TDA.Probability.SamplingCoverage` only, Comparator independently rejects a `sorry`-closed proof; it does not scan the rest of the tree |
| No custom axiom/`opaque`/`unsafe` | `scripts/check-no-custom-axiom.sh` (textual, whole tree) | Partial — same single-module scope; Comparator checks the solution's realised axiom closure against `permitted_axioms`, not the declaration text |
| Live axiom-closure audit (⊆ allowlist) | `scripts/check-axioms.sh` | Partial — overlaps for the one target only; Comparator additionally rejects a changed theorem statement or a changed named definition in its closure, neither of which the axiom audit alone detects |
| Every public theorem pinned, root/area aggregators imports-only | `scripts/check_axiom_coverage.lean`, `scripts/check-root-aggregator.sh` | None — `comparator.json`'s `theorem_names` is the one frozen target, not full coverage; `ComparatorChallenge` is checked by the same root-aggregator guard as any other `[[lean_lib]]` but is not a safeguard Comparator substitutes for |
| Transient/status artefacts, merge-conflict markers rejected | `scripts/check-transient-artifacts.sh`, `scripts/check-conflict-markers.sh` | None |
| Production/challenge import boundary | `scripts/check-comparator.sh` itself (the wrapper's own precondition) | N/A — not a pre-existing guard |
| Source ↔ Lean fidelity of the reference and the target | independent source ↔ Lean review (PR #766 for production; a fresh fidelity review of the reference for this PR) | None — Comparator never reads `docs/math/rips-sampling-confidence.md` |
| Agreement with the reviewed reference statement | nothing else | Comparator only — this is the contract's unique value |

## Consequences and limits

`TDA.lean` does not import `ComparatorChallenge`, and `ComparatorChallenge` is not a default
build target. This pilot establishes agreement between
`TDA.Probability.SamplingCoverage`'s realised statement and this reviewed reference; it does
not establish fidelity to `docs/math/rips-sampling-confidence.md` on its own, and it does not
cover any theorem besides `TDA.Probability.measure_missedCover_le_card_mul`. Extending the
pilot to another target needs its own Issue, its own independently authored and reviewed
reference, and — per the private-constant and universe constraints above — a check of that
target's full statement and named-definition closure for private declarations and universe
names before relying on Comparator's verdict.
