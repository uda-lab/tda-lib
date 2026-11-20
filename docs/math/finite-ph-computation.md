# Certified finite F₂ persistence from simplex lists

## First run

`FiniteInput` and its matching [`Examples.filled` fixture](../../TDA/Persistence/Reduction/FiniteInputExamples.lean)
are present in the [v0.3.0 release](https://github.com/uda-lab/tda-lib/releases/tag/v0.3.0).
The output below was checked against the current checkout.

In an existing Lean/Lake project, make TDA available using the
[project setup instructions](../../README.md#use-in-a-lean-project). From that project's
root, save the block below as `FinitePHExample.lean` and run
`lake env lean FinitePHExample.lean`. The `#eval` commands print the results shown below.

This seven-entry list adds vertices at grade `0`, edges at `1`, and the filled
triangle at `2`:

```lean
import TDA.Persistence.Reduction.FiniteInput

open TDA.Persistence.Reduction.FiniteInput

def filledTriangle : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0),
    ({0, 1}, 1), ({1, 2}, 1), ({0, 2}, 1),
    ({0, 1, 2}, 2)]

#eval validBool filledTriangle
#eval run filledTriangle

def missingEdge : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0),
    ({0, 1}, 1), ({1, 2}, 1),
    ({0, 1, 2}, 2)]

#eval validBool missingEdge
#eval run missingEdge
```

For `filledTriangle`, `validBool` is `true`, and `run` returns `some`
containing the full four-record list shown here, in order:

| Degree | Birth | Death |
|---:|---:|---|
| 0 | 0 | `Death.finite 1` |
| 0 | 0 | `Death.finite 1` |
| 1 | 1 | `Death.finite 2` |
| 0 | 0 | `Death.essential` |

The equal degree-zero rows are separate finite H₀ occurrences. `Death.essential`
represents unbounded death, not an integer sentinel. `missingEdge` omits the
`{0, 2}` edge, so `validBool` is `false` and `run` returns `none`; the input is
not repaired.

For cycles in the original face-index basis and fillings for finite deaths,
continue to [cycle representatives](finite-ph-representatives.md).
That API was added in v0.4.0.

## Contract and representation

`TDA.Persistence.Reduction.FiniteInput.Input` is a list of `(Finset ℕ, ℤ)` pairs. A
list position is a zero-based face index. The natural numbers are vertex labels,
not an ambient vertex interval: only listed nonempty faces belong to `complex`.
Thus an empty list represents the empty complex, and a face using vertex `900`
does not introduce vertices `0` through `899`. The vertex order within a face
is the canonical increasing order given by `Finset.orderEmbOfFin`.

`Valid` records five conditions: nonempty simplices, unique simplices regardless
of grades, presence of every nonempty subset, strict face-before-coface order,
and nondecreasing grades at all ordered list positions. `validBool` decides this
whole proposition by finite list, powerset, natural-order, and integer-order
decisions; `validBool_iff` proves both directions. `run` returns `none` on invalid
data and the computed occurrence list on valid data. `run_isSome_iff`,
`run_eq_some_iff`, and `run_eq_none_iff` link acceptance, successful output, and
rejection exactly. No input normalization is performed. Negative grades, tied
grades, and empty input are valid when the five conditions hold.

For a valid list, `complex` has exactly its listed faces (`mem_complex`), and
`listEquiv` pairs original positions bijectively with its total faces. Its inverse
uses `List.Nodup.getEquiv` and finite `List.idxOf` search on the listed faces;
it does not select a position by choice. `faceFintype` enumerates these faces,
`gradeFilter` reads their original integer grades, and `positionEquiv` and
`compatibleOrder` preserve the given list order. Face precedence together with
nondecreasing list grades proves monotonicity. `sublevelFaceIndex` computes the
same original position for an actual sublevel face, with its grade and degree
laws preserved. Index and grade lookup do not depend on the validity proof.
These finite adapters are computable; actual quotient-homology constructions
and the arbitrary-field decomposition retain their proof-side limitations.
None of the semantic adapters occurs in the transitive definition path of `run`.

## Computation and indices

`boundary` reads faces at two list positions. For a codimension-one candidate
it sums the oriented deletion terms in canonical vertex order, specializing
the signs to `ZMod 2`; all other entries are zero. Its definition uses only
finite indexing, `Finset` deletion and equality, and finite sums. The vertex
column is zero in ordinary **unaugmented** homology. In particular, an isolated
vertex contributes an essential H₀ class. The computation does not insert an
empty face as a chain generator.

`boundary_eq_faceBoundaryMatrix` compares every computed entry with the existing
`faceBoundaryMatrix` under the position equivalence. `boundary_reindex` is
the whole-matrix version. The existing face-boundary theorems then yield
`boundary_sq_zero`, `boundary_strict` (nonzero rows precede their columns),
and `boundary_lowersDegree` (the column degree is one above its row degree).
This bridge uses the signed simplicial deletion convention already formalized
in `SimplicialAdapter.lean`; specializing to F₂ makes each deletion coefficient
one.

`trace` invokes the existing chronological `matrixReductionTrace` on that
computed matrix, and `reduced` invokes `replay`. `reduced_reindex` shows that
this is the `reducedFaceBoundary` used by the semantic certificate.
`pivotPairs` produces one pair `(i,j)` for each nonzero reduced column `j`,
where `i = columnPivot (reduced.col j)`. A pivot at row zero is `some 0`;
`none` means a zero column. `essentialIndices` selects zero columns outside
the image of the pivot map. The two extraction lemmas compare these finite
lists, converted to multisets by degree, with the existing `pivotIndexPairs`
and `pivotEssentialIndices`. Neither path quotients a list to a set, so equal
value intervals can occur more than once.

A pair gets the degree of face `i`, birth grade of face `i`, and finite death
grade of face `j`. An essential index gets its face degree and birth grade,
with the distinct `Death.essential` constructor. `pairOccurrence` drops an
equal-grade finite pair only at the value-output step. `finite_birth_lt_death`
proves that every retained finite occurrence has a strictly later death.
An essential death is interpreted as `⊤ : WithTop ℤ`, never as an integer
sentinel or the largest attained grade. `outputDiagram` filters the occurrence
list by homological degree and maps it to a multiset of diagram points, retaining
duplicate points.

The face indices above start at zero. The face-prefix filtration in the
reduction theorem counts **stages**: face index `i` enters at stage `i+1`.
The finite index-bar death stage is likewise one past its final live prefix.
The index sentinel after all `m` faces is `m+1` in the shifted stage model;
it marks an essential index interval and is not an integer death grade.
After the largest attained integer grade, the semantic sublevel is the full
represented complex, so an essential class persists along the constant tail.
For empty input there is no attained maximum, and the sublevel remains empty.

## Correctness route

`pairValuesAtDegree_semantic` and `essentialBirthsAtDegree_semantic` identify
the computed grade multisets with the existing pivot template's grade maps.
`outputDiagram_points` separates the finite off-diagonal and essential
contributions. The final `outputDiagram_eq_dgm` invokes merged
`evaluatePivotTemplate_eq_dgm` from `SimplicialAdapterTemplate.lean`, which
already connects the boundary reducer and filtered normal form to
simplicial homology. The proof-only
`nonempty_facePrefixHomologyIsoPivotBarcode` additionally exposes the
genuine natural interval isomorphism of that prefix module. Thus, for every valid input and every degree,
the interpreted records equal `dgm (ZMod 2) (gradeFilter xs h) p` as a
`Diagram ℤ`. This is a statement about the integer sublevel filtration,
not a declared pairing or a separately assumed barcode decomposition.

`outputDiagram_eq_of_same_graded_complex` states the order-independence
consequence at the diagram level: valid presentations whose represented
complexes and filters agree have equal interpreted diagrams. The occurrence
list order and position pairs can differ. `Examples.equal_grade_reordering`
checks a concrete equal-grade edge swap whose pivot pairs differ.

`FiniteInputExamples.lean` proves evaluations through the public `run` path,
including the [filled-triangle first run](#first-run). Its zero-based pivot
pairs are `(1,3), (2,4), (5,6)` and its essential index is `0`. Removing the
triangle leaves an essential H₁ birth at `1`; tying the triangle to grade `1`
removes its zero-length value interval. Further fixtures cover empty input, a delayed
single vertex, negative grades, duplicate intervals on disjoint edges,
equal-grade reordering, and sparse vertex labels. Five negative fixtures
reject an empty simplex, duplicate simplex with different grade, missing
face, coface-first list, and decreasing grades. The negative runs together
with `run_eq_none_iff` justify their invalidity.

## Rips input from an integer distance table

`TDA.Persistence.Reduction.RipsInput` computes a simplex list of the format above
from a finite metric given by integers. A `DistanceTable N` is a function
`Fin N → Fin N → ℤ`. `DistanceTable.Valid` is the conjunction of nonnegative
entries, symmetry, zero diagonal, positive distance between distinct labels and
every triangle inequality. It is decidable by finite quantification over the
labels. Nonnegativity follows from the other four conditions and is checked all
the same. An invalid table is rejected, not repaired, and no metric certificate
is supplied by the caller. The table with no label and the table with one label
and entry `0` are valid.

`diameter s` is the maximum entry over the ordered pairs of a set `s` of labels,
with value `0` on the empty set: the same fold as `Rips.diameter`, over the
integers (`diameter_le_iff`, `dist_le_diameter`, `diameter_mono`). A single label
of a valid table has diameter `0` (`diameter_singleton`).

`ripsInput` lists every nonempty set of labels once:

* `faceLists N` enumerates the nonempty strictly increasing label lists, by
  length and then lexicographically (`mem_faceLists`, `nodup_faceLists`).
* `entry` turns a label list into the pair of its set of labels, mapped into the
  vertex type `ℕ` by `Fin.valEmbedding`, and its diameter. The labels
  `0, …, N - 1` are transported into `ℕ`; no metric on `ℕ` is introduced.
* The distinct grades are sorted, and for each grade in increasing order the
  entries of that grade are taken in the order of the enumeration.

`mem_ripsInput` states that the entries are exactly the pairs
`(s.map Fin.valEmbedding, diameter s)` for nonempty `s`, and `mk_mem_ripsInput`
that the grade listed with a face is its diameter. `ripsInput_pairwise` states
the order: by grade, then by cardinality, then lexicographically in the
increasing label lists. Each face occurs once (`nodup_faces_ripsInput`) and the
list has `2 ^ N - 1` entries (`length_ripsInput`). The tie-break is a property
of this implementation; by `outputDiagram_eq_of_same_graded_complex` the
interpreted diagram does not depend on it.

`ripsInput_valid` proves the five conditions of `Valid` for the list. It holds
for every table, valid or not, because the maximum over pairs is monotone in the
set; only the metric meaning of the list needs a valid table. `ripsInput?`
returns the list for a valid table and `none` otherwise. `ripsRun` returns
`occurrences` of the list for a valid table and `none` otherwise; it does not
decide `Valid` of the list again, and `ripsRun_eq_bind_run` states that its
value is that of `run` on the validated list.

For a valid table, `metric` is the metric on `Fin N` whose distances are the
table entries, passed explicitly to the Rips API and not registered as an
instance. `cast_diameter` identifies the integer diameter, cast to a real
number, with `Rips.diameter`. The represented complex `complex` of the list is
the image of `Rips.fullComplex (Fin N)` under the inclusion of labels
(`mem_complex_ripsInput`, `complex_ripsInput`), `ripsFace` is the resulting
bijection of faces (`ripsFace_bijective`), and `gradeFilter_ripsFace` states
that the grade read by `gradeFilter` at a face, cast to a real number, is the
value of `Rips.filter` for `metric` at the corresponding face. These are
statements about the complex and the filter that `outputDiagram_eq_dgm` uses.

This module does not compare diagrams or homology. The equality of
`outputDiagram` of the list with the diagram of `Rips.filter`, and the
positive-degree consumer for the four-cycle, are later units.

Write `F = 2 ^ N - 1` for the number of faces and `G` for the number of
distinct grades; every grade is `0` or a table entry, so
`G ≤ N (N - 1) / 2 + 1` for a valid table. Counting a table lookup, a comparison
or maximum of two integers and a comparison of two labels as one unit:
validation costs `O(N³)` comparisons and additions; forming the sets of labels
and their diameters costs `O(N² F)`; collecting the distinct grades costs
`O(F G)`, sorting them `O(G²)` and grouping the entries by grade `O(F G)`. The
list costs `O(N² F) = O(N² 2 ^ N)` units, which is exponential in `N`, and an
integer unit costs time proportional to the bit length of the entries. `ripsRun`
adds the cost of the existing reduction on `F` faces, which is not bounded here;
it is at least quadratic in `F`, since the boundary matrix is a dense `F × F`
matrix, and it dominates already for small tables. These counts are documented,
not proved. The executable definitions use lists, finite sets given by lists and
integer comparison, with no decision by `Classical` and no real-number
comparison; `metric` and the statements about `Rips` are semantic adapters.

`RipsInputExamples.lean` states the complete value of `ripsInput?` for no label,
one label, two labels at distance `3`, three labels at mutual distance `2`
(four faces of one grade, listed by cardinality and label order), three points
on a line and the same points with two labels exchanged (`relabelled_dist`,
`relabelled_grades`), and the shortest-path metric of the four-cycle: vertices
at `0`, the four edges at `1`, and both diagonals, the triangles and the
tetrahedron at `2`. `fourCycle_diagonal` transfers the grade `2` of a diagonal
to the value of the actual `Rips.filter`. `ripsRun` is checked for no label,
one label and two labels (`pair_ripsRun`: one finite class from `0` to `3` and
one essential class in degree zero). Tables violating symmetry, separation,
the triangle inequality, the zero diagonal or nonnegativity return `none` from
`ripsInput?` and from `ripsRun`.

## Dependency and source scope

The computational dependencies are pinned Lean/mathlib finite lists and
sets, `Finset.orderEmbOfFin`, integer comparisons, `ZMod 2`, `Matrix`, the
existing `columnPivot`, `matrixReductionTrace`, and `replay`. The semantic
chain uses `SimplicialAdapter.lean` for the signed boundary;
`FilteredNormalForm.lean` for the reducer-to-normal-form theorem;
`SimplicialAdapterTemplate.lean` for the merged simplicial-homology diagram
equality; and `SublevelDiagram.lean`/`IndexDiagram.lean` for the value
diagram and essential-tail interpretation. The earlier mathematical source
inventory and precise correspondence for reduction are in
[persistence-reduction.md](persistence-reduction.md), and the sublevel
convention is in [finite-sublevel-diagram.md](finite-sublevel-diagram.md).
This unit specializes those results to finite F₂ input with integer grades.
It adds no sparse-matrix optimization, file parser, real-grade computation,
or performance bound.
