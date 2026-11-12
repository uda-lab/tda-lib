# Cycle representatives for finite F₂ persistence

`FiniteInput.runWithRepresentatives` returns a chain for each occurrence of the
[finite simplex-list computation](finite-ph-computation.md). It accepts the same
valid lists, uses F₂ coefficients and integer grades, and rejects invalid input
without repairing it. Import
`TDA.Persistence.Reduction.FiniteInputRepresentativeCorrectness` for the executable
API and its simplicial homology guarantees.

This representative API is an unreleased `develop` addition after v0.3.0.
The [v0.3.0 computation guide](https://github.com/uda-lab/tda-lib/blob/v0.3.0/docs/math/finite-ph-computation.md)
describes the released occurrence-only `run` API.

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

## Integer sublevels and inclusion maps

`runAtGrade xs a` filters the original represented output at an integer grade `a`.
An occurrence is active when its birth is at most `a` and its finite death is
strictly greater than `a`; an essential occurrence has no upper endpoint. The
query preserves order, duplicates, face identities and chain data. Invalid input
returns `none`; valid input with no active occurrence returns `some []`.
`runAtGrade_eq_some_iff`, `mem_runAtGrade` and `runAtGrade_forget` give the successful
output, membership and exact filtered-occurrence projection.

```lean
import TDA.Persistence.Reduction.FiniteInputSublevelHomology
import TDA.Persistence.Reduction.FiniteInputExamples

open TDA.Persistence.Reduction.FiniteInput

#eval runAtGrade Examples.filled 0 -- two finite H₀ records and essential H₀
#eval runAtGrade Examples.filled 1 -- finite H₁ and essential H₀
#eval runAtGrade Examples.filled 2 -- essential H₀
```

`sublevelStage xs a` computes the number of admitted faces directly from the
input. `sublevelStage_eq_count` and `sublevel_eq_prefix` identify the actual integer
sublevel with that prefix; every face tied at grade `a` is admitted together.

Retain a record `r` from `runWithRepresentatives` when following it through time.
For every `a` at or above its birth, `sublevelCycle` includes its computed chain
from the birth prefix into `(gradeFilter xs h).sublevel a`. Its coordinate theorem
recovers `chainVector r.cycle` in the original face basis. `sublevelClass` is the
actual simplicial homology class of this chain, defined even after death.

For `birth ≤ a ≤ b`, `sublevelClass_naturality` proves that the actual homology
inclusion sends the class at `a` to this same chain's class at `b`.
`sublevelClass_nonzero_iff` identifies nonzeroness exactly with the occurrence's
half-open value interval. At an active grade, `sublevelClass_coordinate` gives the
unit vector at the original birth face under the existing prefix/alive equivalence.
At or above finite death, `sublevel_bounding` places the returned filling in the
actual sublevel with its original coefficients and signed boundary identity, and
`sublevelClass_eq_zero_of_death` proves that the class is zero. Essential classes
remain nonzero along the constant tail.

The naturality law starts at birth. It does not identify a prebirth zero class
with a later nonzero generator. A record removed by a later `runAtGrade` query
still has a defined, zero `sublevelClass` there. These individual class laws do
not require choosing a new representative at each threshold.

## Complete bases and inclusion coordinates

For a degree `p` and integer threshold `a`, `runDegreeAtGrade xs p a` filters
`runAtGrade xs a` by degree. It returns the same records in their existing order,
including different records whose interval values coincide. Invalid input returns
`none`. For valid input, the output is `activeRepresentatives xs p a`;
`BasisIndex xs p a` is the finite type of positions in that list, and
`basisRecord xs p a i` retrieves the record at position `i`.

These positions index a basis of the actual simplicial homology of the sublevel.
`basisClass xs h p a i` is the existing `sublevelClass` of the exact computed
cycle at that position, with its degree identified with `p`.
`sublevelBasis_apply` proves that `sublevelBasis` consists of these classes.
`basisRecord_birth_bijective` proves completeness and uniqueness: every alive
normal-form birth coordinate is present exactly once. In particular, the two
finite H₀ records of the filled triangle give different basis vectors at grade
zero, despite having equal interval values.

`sublevelCoordinates xs h p a` is a linear equivalence from the entire actual
homology group to F₂-valued functions on `BasisIndex xs p a`. It reads the
existing normal-form coordinates in query order. `sublevelCoordinates_basisClass`
sends the computed class at position `i` to its unit vector.
`sublevelClass_expansion` expresses any class as the sum of these computed
classes with its coordinate coefficients; `sublevelClass_unique_expansion`
proves uniqueness. `sublevelHomology_finrank` identifies the dimension with the
query length. The empty query therefore gives zero homology, rather than merely
no selected witnesses.

For `a ≤ b`, `basisTransition xs p a b` has target-query rows and source-query
columns. Its entry is one exactly when the two records have the same original
birth index. Positions can change as records disappear, and interval values can
coincide, so neither is used to match records. The theorem
`sublevelCoordinates_naturality` states, for every actual homology class `x`,

```text
coordinates at b (inclusion a→b x) = transition a→b · coordinates at a x.
```

A dying source record gives a zero column. A later-born target record gives a
zero row. A surviving record retains its coefficient even if its list position
changes. For example, the valid input
`[({0},0), ({1},0), ({0,1},1), ({2},1)]` has H₀ birth-index lists `[1,0]`
at grade zero and `[0,3]` at grade one. Its inclusion matrix is
`[[0,1], [0,0]]`: the finite class dies, the first essential class survives,
and the isolated vertex is born. `basisTransition_self` and
`basisTransition_comp` give identity and composition laws.

```lean
import TDA.Persistence.Reduction.FiniteInputSublevelBasisExamples

open TDA.Persistence.Reduction.FiniteInput

#eval (runDegreeAtGrade Examples.filled 0 0).map
  (List.map (fun r => r.birthIndex.val)) -- some [1, 2, 0]
#eval (runDegreeAtGrade BasisExamples.mixed 0 1).map
  (List.map (fun r => r.birthIndex.val)) -- some [0, 3]
```

The query and matrix use finite computation. The basis and coordinate equivalence
are proof-side, noncomputable semantic objects. `FiniteInputSublevelBasisExamples.lean`
checks complete dimensions, unique expansion, the filled H₁ death map, essential
H₁, duplicate H₀, negative/tied grades, empty/invalid input and the mixed inclusion
above. The construction reuses the proved normal-form and actual simplicial
adapters, without a basis or completeness certificate supplied by the caller.

## Computing the coordinates of a supplied cycle

Supply a coefficient vector `v : Fin xs.length → ZMod 2` in the original face
order to `runCycleCoordinates xs p a v`. It validates the simplex input and
checks that every nonzero entry is a degree-`p` face admitted at grade `a`, and
that the original signed boundary of `v` is zero. A failed check returns `none`.
Success returns a coefficient list in exactly the order of
`runDegreeAtGrade xs p a`. The zero vector is accepted for every degree and
threshold when the simplex input is valid, including empty input.

For the filled triangle, the degree-zero basis at grade zero consists of the two
finite cycles and the essential cycle in the first table. Individual vertices,
which need not be selected representatives, therefore have these coordinates:

| Supplied vector | Grade 0 | Grade 1 |
|---|---|---|
| vertex 0 | `[0,0,1]` | `[1]` |
| vertex 1 | `[1,0,1]` | `[1]` |
| vertex 2 | `[1,1,1]` | `[1]` |
| vertices 0 + 1 | `[1,0,0]` | `[0]` |

At grade one the vertices are homologous, and the nonzero chain consisting of
vertices 0 and 1 is the boundary of an edge. Zero coefficients mean a zero
homology class, not necessarily a zero chain. Likewise, the three-edge H₁ cycle
has coefficient `[1]` at grade one and coefficient list `[]` at grade two, where
the triangle fills it. A hollow triangle retains coefficient `[1]` on its
essential tail. Equal-grade omission still applies to value-level coordinates.

```lean
import TDA.Persistence.Reduction.FiniteInputCycleCoordinatesCorrectness
import TDA.Persistence.Reduction.FiniteInputExamples

open TDA.Persistence.Reduction.FiniteInput

#eval runCycleCoordinates Examples.filled 0 0
  (fun i => if i.val = 1 then 1 else 0) -- some [1, 0, 1]
#eval runCycleCoordinates Examples.filled 0 1
  (fun i => if i.val = 1 then 1 else 0) -- some [1]
#eval runCycleCoordinates Examples.filled 1 2
  (fun i => if i.val ∈ [3, 4, 5] then 1 else 0) -- some []
```

`runCycleCoordinates_eq_some_iff` characterizes the exact validation conditions
and ordered output; `runCycleCoordinates_length` and `runCycleCoordinates_get`
give its length and indexed coefficients. `runCycleCoordinates_correct` proves
that every successful list is the actual `sublevelCoordinates` of the supplied
cycle's simplicial homology class. `vectorSublevelCycle_coordinates` preserves
its original face coefficients. No inverse, basis, class or cycle certificate is
an input to the executed procedure.

The raw linear map `rawCycleCoordinates` also accepts arbitrary vectors, with
its homological meaning restricted to the predicate `CycleInput`.
`rawCycleCoordinates_eq_zero_iff_boundary` identifies its kernel on admitted
cycles with the actual simplicial boundary submodule.
`rawCycleCoordinates_eq_iff` characterizes equality of their actual classes.
`rawCycleCoordinates_naturality` computes how a cycle's coefficients change
under integer-sublevel inclusion using the same `basisTransition` matrix.
`runCycleCoordinates_basisRecord` is the round-trip law: each selected cycle
returns its own unit coordinate in query order, including duplicate-valued bars.

The executable inverse uses the same normal matrix `N`, selected by finite
search through all pivot pairs and the change columns. It includes tied-grade
pairs in this matrix even when the value query omits them. For `n` faces,
`U = 1 - N` is strictly upper triangular and `U^n = 0`. Starting with `G₀ = 0`,
the finite iteration `Gₖ₊₁ = 1 + Gₖ U` produces `N⁻¹` after `n` steps. Fixed-size
vectors store the intermediate matrix entries. `normalCoordinateVector_apply`
proves agreement with the existing normal-form inverse. The executed path uses
neither the proof-only death-index choice nor a noncomputable matrix inverse.
No optimal complexity is claimed. `FiniteInputCycleCoordinatesExamples.lean` checks supplied vertices,
homologous distinct cycles, a nonzero boundary, changed query positions and the
triangle, essential, tied/negative, zero/empty and rejection cases.

## Constructing a filling for a supplied boundary

`runCycleFilling xs p a v` returns a chain whose boundary is the supplied vector
`v`, using the same input, degree and sublevel checks as `runCycleCoordinates`.
It succeeds exactly when those checks pass and every homology coefficient is
zero. Thus a nonempty coefficient list such as `[0]` is accepted. A valid zero
vector returns `some []` at every degree and threshold, including empty input.
Invalid input, a vector that fails the cycle checks, or a nonzero homology class
returns `none`.

Success returns `some b`, where `b` is a duplicate-free list of original face
indices. Each listed face has coefficient one. The decoded vector
`chainVector b` has degree `p+1`, is supported in the sublevel at `a`, and has
signed simplicial boundary exactly `v`.

```lean
import TDA.Persistence.Reduction.FiniteInputCycleFillingCorrectness
import TDA.Persistence.Reduction.FiniteInputExamples

open TDA.Persistence.Reduction.FiniteInput

#eval runCycleFilling Examples.filled 1 2
  (fun i => if i.val ∈ [3, 4, 5] then 1 else 0) -- some [6]
#eval runCycleFilling Examples.filled 0 1
  (fun i => if i.val ∈ [0, 2] then 1 else 0) -- some [3, 4]
#eval runCycleFilling Examples.hollow 1 100
  (fun i => if i.val ∈ [3, 4, 5] then 1 else 0) -- none
```

The first result fills the three triangle edges with the triangle. The second
fills a pair of vertices with two edges selected by the reduction trace, even
though another edge alone has the same boundary. A selected filling therefore
need not have the fewest faces. A tied-grade triangle is also filled at its
common grade: the algorithm uses all reduced pivot pairs, including those
omitted from the value barcode.

`runCycleFilling_eq_some_iff` supplies validity, cycle admission, the zero-coordinate
condition and the exact selected output. `runCycleFilling_data` proves the decoded
support, degree and matrix-boundary laws. `runCycleFilling_correct` constructs an
actual chain in `(gradeFilter xs h).sublevel a` with those original coefficients
and proves that its actual signed boundary is `vectorSublevelCycle` of `v`.
On admitted cycles, `runCycleFilling_exists_iff_boundary` identifies successful
execution with membership in the actual simplicial boundary submodule. These
results require no supplied filling or boundary certificate.

To compute the filling, let `x = N⁻¹ v` be the executable normal coordinates.
For each reduced death column `j` with pivot `i`, select coefficient
`x i / R i j` when `j` is admitted and `i` has degree `p`, and zero otherwise.
The change matrix `V` sends this selected vector to the original-face filling.
`fillingVector_eq` identifies the computation with `expiredPreimage` followed by
`V`. The normal-cycle decomposition proves its boundary identity; death columns
are nonpivots, so `N` and `V` agree on this preimage. All choices in execution are
finite searches and arithmetic. Actual chain objects and matrix inverses occur
only in the correctness proofs.

`FiniteInputCycleFillingExamples.lean` checks triangle and multiple-edge fillings,
essential classes, tied and negative grades, nonempty zero coordinates, zero and
empty inputs, and validation failures. It also consumes the public signed-boundary
and actual-chain guarantees.

To compute maps between different finite inputs, including vertex functions
that merge vertices, see [computing finite homology maps](finite-ph-maps.md).

## Value intervals and scope

Integer grades are separate from prefix stages. As in `run`, a pivot pair whose
birth and death grades agree is omitted from the value output. In `Examples.tied`
the H₁ index class is nonzero at prefix 6, but both its birth and its death have
grade 1, so no H₁ value interval is returned and the H₁ integer-sublevel basis is
empty. The bases at different thresholds are compatible through the transition
matrices above; an inclusion need not send every source basis vector to a
nonzero target basis vector.

The representative depends on the supplied face order and this reduction trace.
No shortestness, canonicity or order-independence of representatives is claimed.
The coefficient field and grade type remain F₂ and integers. The contract is a
library-derived computational extension of the existing Lean definitions and
proved adapters. It does not assert a new comparison against primary-paper text.
