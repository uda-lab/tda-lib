# Certified finite F₂ persistence from simplex lists

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
`listEquiv` pairs positions bijectively with its total faces. `gradeFilter`
assigns each face its unique listed integer grade. Face precedence together
with nondecreasing list grades proves monotonicity. `compatibleOrder` takes
the given list order as the compatible face enumeration. These semantic
objects and their proof-derived equivalences may be noncomputable; none occurs
in the transitive definition path of `run`.

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

`FiniteInputExamples.lean` proves evaluations through the public `run` path.
The filled triangle has zero-based pairs `(1,3), (2,4), (5,6)` and essential
index `0`, yielding two `(0,1)` finite H₀ occurrences, one essential H₀
birth at `0`, and a finite H₁ `(1,2)`. Removing the triangle leaves an
essential H₁ birth at `1`; tying the triangle to grade `1` removes its
zero-length value interval. Further fixtures cover empty input, a delayed
single vertex, negative grades, duplicate intervals on disjoint edges,
equal-grade reordering, and sparse vertex labels. Five negative fixtures
reject an empty simplex, duplicate simplex with different grade, missing
face, coface-first list, and decreasing grades. The negative runs together
with `run_eq_none_iff` justify their invalidity.

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
