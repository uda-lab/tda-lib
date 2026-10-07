---
name: lean-issue-decomposition
description: Turn a mathematical digest (docs/math) into an executable GitHub Issue queue for a Lean formalisation loop — statement-contract Issue first, worker-sized source-anchored block Issues, dependency graph on the charter, agent:ready audit, and the ruled-design comment a driver executes. Use in Init Phase 4 and whenever an Issue turns out larger than filed.
---

# lean-issue-decomposition

Input: the charter Issue and `docs/math/<digest>.md`. Output: Issues an orchestrator can
dispatch one at a time with a ruled design, each closable by one driver with worker jobs of
≤ 400 Lean lines. No planning document is produced; the Issues and the charter's milestone
list *are* the plan.

## 1. Statement contract first

The first Issue (M1) fixes the target's Lean statements before any proof: a `Contract.lean`
(or equivalently named module) holding the main theorem(s) and the interface they quantify
over, stated in the source's vocabulary, with every convention choice written in the
docstring (sign, normalisation, quantifier order, domain, topology).

A public `theorem … := by sorry` cannot land under the scaffold's gates: the coverage guard
pins every public theorem and the live audit rejects `sorryAx` on every pinned name. State
the holes with one of two devices:

- **Private theorems** (default): `private theorem … := by sorry -- ALLOW_SORRY: #<M1>
  statement contract`. Private declarations are neither public nor pinned, so the contract
  compiles and the gate stays green; the proving PR removes `private` and appends the name
  to `scripts/print_axioms.lean`. The frozen text is a literal theorem from day one, so a
  later PR is diffed against it byte for byte.
- **Prop interface**: `def <Target> … : Prop := …` carrying the full statement, with the
  final theorem signatures quoted in its docstring; the proving PR states the theorems with
  that Prop as conclusion and pins them. Use it when the interface itself is the
  deliverable (several theorems share one hypothesis bundle). The frozen text then lives in
  a docstring and the reviewer must unfold the Prop to read the claim.

Acceptance criteria of M1: a judge distinct from the implementer records a source ↔ Lean audit
on the Issue; `scripts/check.sh` is green with the holes in place. From then on **the statement
text is frozen**: a PR that changes it is statement-changing and needs the same audit again.
The contract Issue also says what is frozen as interface — the exact public names and types,
or only the source-form statements, or only a proof of the source results — so reviewers can
tell a contract violation from a legitimate stronger result (`lean-review-routing`
§ Contract-aware comparison).

## 2. Block Issues

Walk the source's lemma route backwards from the target. For each node (a primary source that
is unavailable is handled by the unavailable-source fallback of `loop-orchestration-scaffold`
Phase 0: marked anchor, `digest-based` audit, comparison kept open on the charter):

- **Source anchor**: paper, theorem/lemma/equation number, page; the literal claim with the
  source's hypotheses (the Issue template's fields are mandatory).
- **Lean target**: a signature or a precise semantic target with domains and quantifier order;
  name the declarations it will export and which contract holes it discharges.
- **Size**: one driver, worker jobs of ≤ 400 Lean lines, roughly ≤ 1500 lines total. Larger
  → split by lemma group or by "interface Issue + instance Issue". A block that needs a
  mathlib API the source does not mention gets its own recon Issue (judge or worker, read-only:
  API sweep, no Lean written).
- **Dependencies**: Issues, declarations on `main` by name, mathlib. Dependencies merged or
  explicitly out of scope before `agent:ready`.
- **Ambiguities**: every place the source is implicit; the Issue decides them or names the
  judge that will.
- **Acceptance**: declarations by name, sorry-free, pinned in `scripts/print_axioms.lean`,
  `scripts/check.sh` green, review evidence; for source-sensitive blocks the correspondence
  section of the PR filled.

Order by danger, not ease (`lean-formalization-discipline`): the load-bearing analytic step,
the hypothesis most likely to be unprovable as stated, and the mathlib gap go first, while
the loop still has budget to change the route. Cheap connected wins are filler, not progress.

## 3. Dependency graph on the charter

Append the milestone list and an ASCII dependency graph to the charter Issue; tick milestones
as PRs merge (the orchestrator edits, drivers do not). No separate roadmap file.

## 4. `agent:ready` audit

Only the owner or the trusted maintainer applies `agent:ready`, after recording on the Issue:

1. scope and acceptance criteria are explicit and machine-checkable where possible;
2. for source-sensitive work, the source audit by an agent distinct from the eventual
   implementer (judge, reasoning tier, read-only: literal claim vs source, hypotheses
   preserved, no proxy assumptions), in the mode actually used — a `digest-based` audit under
   the unavailable-source fallback makes the Issue executable, not source-verified;
3. dependencies merged or explicitly out of scope; no hard-stop label.

## 5. The ruled-design comment

Before dispatch the orchestrator posts one comment on the Issue that the driver executes:

```
### Ruling: route and inputs
Route: <the proof route in 3–6 steps, each naming the source lemma it follows>
Discharge: <declarations, byte-identical to the contract>
Inputs on main: <declarations by fully qualified name, file>
Do not: <the shortcuts the source does not license — proxy hypotheses, a stronger axiom, a
symmetry the theory does not have>
Traps: <mathlib API gaps, convention mismatches, earlier review findings>
Worker policy: <tier per block, resolved to the contract's model/effort>
```

Everything a driver would otherwise have to guess goes here; a routine-tier driver with a
ruled design outperforms an unruled reasoning-tier driver. When a driver escalates a fork, the
answer is a second ruling comment, not a message.

## 6. Re-decomposition

An Issue larger than filed is split by the orchestrator into child Issues linked from the
parent; the driver keeps the parent's branch for the part it can finish and pushes a
gate-green commit before stopping. Never widen an Issue in flight.
