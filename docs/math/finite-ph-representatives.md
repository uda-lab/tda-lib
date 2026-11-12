# Cycle representatives for finite F₂ persistence

`FiniteInput.runWithRepresentatives` returns a chain for each occurrence of the
[finite simplex-list computation](finite-ph-computation.md). It accepts the same
valid lists, uses F₂ coefficients and integer grades, and rejects invalid input
without repairing it. Import
`TDA.Persistence.Reduction.FiniteInputRepresentativeCorrectness` for the executable
API and its simplicial homology guarantees.

## Read the output

A `Representative xs.length` contains the unchanged `occurrence`, a `birthIndex`,
an optional `deathIndex`, a `cycle` and an optional `bounding` chain. Each chain is
an increasing list of original, zero-based face indices. Every listed index has
coefficient one; other indices have coefficient zero. `chainVector` decodes this
support-list representation. Returned cycles have no repeated indices
(`returned_cycle_nodup`).

For the filled triangle in `FiniteInput.Examples.filled`, the output is:

| Degree | Value interval | Birth index | Death index | Cycle | Bounding chain |
|---:|---|---:|---:|---|---|
| 0 | [0, 1) | 1 | 3 | [0, 1] | [3] |
| 0 | [0, 1) | 2 | 4 | [1, 2] | [4] |
| 1 | [1, 2) | 5 | 6 | [3, 4, 5] | [6] |
| 0 | [0, ∞) | 0 | none | [0] | none |

The H₁ cycle is the sum of the three edges; its filling is the triangle. The two
finite H₀ records have equal value intervals and distinct original birth faces.
Deleting the triangle makes `[3, 4, 5]` an essential H₁ cycle, with no filling in
the output. An isolated vertex gives an essential H₀ cycle in ordinary,
unaugmented homology.

```lean
import TDA.Persistence.Reduction.FiniteInputRepresentativeCorrectness
import TDA.Persistence.Reduction.FiniteInputExamples

open TDA.Persistence.Reduction.FiniteInput

#eval runWithRepresentatives Examples.filled
#eval runWithRepresentatives Examples.hollow
#eval runWithRepresentatives Examples.tied
#eval runWithRepresentatives []
```

`runWithRepresentatives_forget` proves that mapping every returned record to its
`occurrence` gives exactly `run xs`, including rejection, multiplicities and list
order. `runWithRepresentatives_eq_some_iff` supplies validity and identifies the
returned list with `representedOccurrences xs`; its membership hypotheses feed
the correctness theorems. `returned_identity` reads the birth and death grades
from the recorded original indices and identifies when a filling is present.

## The selected chains

Write `D` for the computed signed simplicial boundary over F₂, `R` for its reduced
matrix and `V = traceChange (trace xs)` for the chronological change matrix. For
a pivot pair `(i,j)`, the cycle is the support of
`(R i j)⁻¹ • R.col j`. Its bounding chain is the support of `V.col j`. A nonzero
F₂ pivot is one, so `D * V.col j` is exactly the normalized cycle. For an essential
index `i`, the cycle is the support of `V.col i`.

The executable path uses finite pivot-pair and essential-index extraction and
`traceChange`. It does not evaluate the proof-only `normalColumn`, its chosen
death index, a matrix inverse or the semantic face enumeration.
`pairedVector_eq_normalColumn`, `essentialVector_eq_normalColumn` and
`returned_normalColumn` prove agreement with the existing normal-form choice.

## Prefix and homology guarantees

A face index `i` enters at prefix stage `i+1`. A finite pair `(i,j)` is alive at
stages `i < t ≤ j` and dies at stage `j+1`. The actual prefix-stage API uses
`t : Fin (xs.length + 1)`, including the empty and full prefixes.

For every member of the returned list:

- `returned_birth_cycle` proves support in prefix `i+1`, the occurrence's chain
  degree and zero boundary for the computed signed matrix.
- `returned_bounding` proves the filling's support in prefix `j+1`, its degree
  one above the cycle and its boundary identity. `returned_simplicial_bounding`
  transports this identity to the actual signed simplicial boundary.
- `representedCycle` is an actual simplicial cycle at each alive prefix.
  `representedCycle_coordinates` identifies its coefficients with the returned
  support list under the existing `prefixChainEquiv`.
- `representedClass_nonzero` proves its class is nonzero in actual
  `simplicialHomology`. `representedClass_coordinate` proves that the existing
  prefix-homology and normal-form/alive-space isomorphisms send it to the unit
  coordinate indexed by that occurrence's original birth face.
  `representedCycle_liveMap` gives the same unit directly under `prefixCycleToLive`. Validity and
  output membership supply all reduction and normal-form hypotheses.

These statements reuse the existing simplicial adapter and filtered normal form;
they do not assume a supplied cycle, filling, decomposition or nonzero class.
`FiniteInputRepresentativeExamples.lean` checks the public executions and their
semantic consumers for filled and hollow triangles, essential H₀, duplicate
occurrences, tied grades, empty input and invalid input.

## Value intervals and scope

Integer grades are separate from prefix stages. As in `run`, a pivot pair whose
birth and death grades agree is omitted from the value output. In `Examples.tied`
the H₁ index class is nonzero at prefix 6, but both its birth and its death have
grade 1, so no H₁ value interval is returned. The theorem does not assert an
integer-sublevel natural-basis API for these chosen chains.

The representative depends on the supplied face order and this reduction trace.
No shortestness, canonicity or order-independence of representatives is claimed.
The coefficient field and grade type remain F₂ and integers. The contract is a
library-derived computational extension of the existing Lean definitions and
proved adapters. It does not assert a new comparison against primary-paper text;
no such text was used as input for this extension.
