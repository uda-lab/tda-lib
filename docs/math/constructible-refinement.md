# Common grids, shifts and refinement-invariant diagrams

Finite-constructible real modules can be placed on a common finite grid without
changing their real endpoint diagrams. The grid may add observations before,
between and after the old critical values. Positive evaluation shifts move
critical values left. These constructions supply actual grid data for comparing
a module with a shifted target.

## Grids and constructibility

A grid is a strictly increasing `c : Fin n ↪o ℝ`, including `n=0`.
`FiniteConstructible.cellIndex c t` counts critical values at or below t.
Its cells are a zero left tail, left-closed/right-open cells between successive
values, and an unbounded final cell. No sentinel real grade represents the zero
cell. The [reconstruction API](constructible-modules.md) defines
`IsConstructible c M` using an actual zero left tail and isomorphic actual
structure maps within each cell.

Constructibility results work for `M : PModule.{u,0,w} R ℝ` over a ring,
with independent coefficient and carrier universes. Barcode and dimension
results below use a field `k : Type u`, carrier universe `u`, and finite
dimensionality at the original critical fibers.

`Refines c d` means that the range of c is contained in the range of d.
It derives a unique increasing embedding e of critical indices with
`d(e i)=c i`. The function `commonGrid c d` orders the finite union of their
critical-value sets. Shared critical values occur once in the union grid;
equal barcode occurrences retain their multiplicity.

If two parameters have the same d-cell, every c-critical value has the same
comparison with both parameters, so their c-cells agree. Therefore
`IsConstructible.refine` transfers constructibility from c to d. A parameter
below every d-value is also below every c-value, preserving the zero left tail.

## Positive evaluation shifts

For finite nonnegative `ε : ℝ≥0`, the actual shift satisfies
`(SεM)(t)=M(t+ε)`. The grid `shiftGrid ε c` has values `c_i-ε`, and

\[
\operatorname{cellIndex}(c-\varepsilon,t)
 =\operatorname{cellIndex}(c,t+\varepsilon).
\]

This identity proves `IsConstructible.shift` for the actual shifted module,
including negative shifted critical values, exact critical parameters and the
whole right tail. At ε=0 the shifted grid equals c. Empty grids select no stage.

For M constructible on c and N constructible on d,
`common_shift_constructible` places both M and `SεN` on the constructed
`commonGrid c (shiftGrid ε d)`. No common-grid witness is supplied as input.

## Finiteness and the diagram on a refinement

Suppose M is c-constructible and its original critical fibers are finite
dimensional. The actual reconstruction component identifies each real fiber
with its finite sample fiber, which is either zero or an original critical
fiber. Thus `finiteDimensional_of_isConstructible` derives finiteness everywhere,
including at all added d-critical values.

The existing `moduleDiagram c M` assigns real endpoints to the canonical rank
barcode of the critical samples. Its terminal index means the constant essential
tail. Under `Refines c d`, `moduleDiagram_refinement` proves equality of the two
actual diagrams. Finite-index barcodes on c and d have different types and are
related by monotone sampling; the equality is of their real endpoint multisets.

Let A be the coarse sample with its initial zero stage. Sample its reconstruction
at the fine critical parameters using

\[
q(j)=\operatorname{cellIndex}(c,d_j)\in\operatorname{Fin}(n+1).
\]

Whiskering the actual reconstruction isomorphism identifies this module with the
fine samples of M. Finite rank-barcode invariance and `rankBarcode_reindex`
therefore restrict each original occurrence along q.

For an old positive observed endpoint r, with `1≤r≤n`, its endpoint cut is
exactly the position `e(r-1)` of `c_(r-1)` in d. At terminal endpoint `r=n+1`
the cut is m, the fine grid size. Every old barcode birth is positive because
the padded zero stage contributes no bars. Strict increase of e makes every
restricted occurrence nonempty. Consequently both finite endpoints recover
the same real values, while terminal death remains infinity even when d adds
later observations. Applying this identity occurrence by occurrence through
`Multiset.filterMap` also preserves duplicates.

## Boundary consumers

An actual rational module reconstructed on `[1,3]` has two copies of `[1,3)`
and one essential bar `[3,∞)`. Refining to `[-2,1,2,3,8]` gives exactly the same
real endpoint multiset. The new observation at 8 creates no finite death for the
essential occurrence. The grid `[1,2]` fails refinement because it omits 3.

At ε=2 the original critical values become `[-1,1]`. The exact first boundary
belongs to its new cell, and the last cell still contains time 100. The union
with `[1,3]` has three distinct values because 1 is shared. Zero shift and
refinement of the zero module from an empty grid are also checked in
`TDA.Persistence.ConstructibleRefinementExamples`.

## Source correspondence and scope

[Bauer–Lesnick v4](https://arxiv.org/html/1311.3681v4), §2.1, supplies the actual
functor, interval and multiset-barcode semantics. Section 3.1 evaluates a shift
at `t+ε`; the barcode correspondence preceding Theorem 6.4 in §6.1 moves its
endpoints left by ε, with the inverse correspondence adding ε.
The zero-left/right-continuous finite grid model and its refinement theorem are
library constructions proved using existing finite reconstruction and rank
results. They are not attributed to a numbered source refinement theorem or to
an inspected proof of general infinite decomposition. Source and rights metadata
are recorded in [BL15-v4](references.md#BL15-v4).

Constructibility of actual kernels and cokernels, sampling of morphisms and
shortness, a diagram formula for real shifts, and the interleaving-to-matching
distance inequality remain separate results. No claim that arbitrary submodules
of constructible modules are constructible is used. The
[actual real defect annihilation](real-interleaving-shortness.md) and
[finite quantitative induced matching](finite-quantitative-induced-matching.md)
results retain their hypotheses until these further bridges are proved.
