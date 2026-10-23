# Ambient Čech Hausdorff stability

Fix one ambient metric space Z. A labelled configuration p : V → Z may repeat points;
its faces are nonempty finite subsets of labels. The **radius filter** assigns a face
the infimum, over all centers in Z, of its largest distance to the face's points.
The **closed-ball complex** at radius r consists of faces with an actual center at
distance at most r from every point. The complex lies in the radius-filter sublevel;
they agree when Z is proper. Both filtrations are empty below zero.

Fix a coefficient field k and a homological degree n ≥ 0. For finite nonempty label
types V and W and configurations p : V → Z, q : W → Z, the full homology diagrams satisfy

```
bottleneck(dgm k (Cech.filter p) n, dgm k (Cech.filter q) n)
  ≤ hausdorffDist(range p, range q).
```

The diagrams include essential bars. The auxiliary label orders need not relate to the
geometry. Cardinalities may
differ and coordinates may repeat. The constant is one because time is ball radius.
The ambient space and possible centers stay fixed throughout the comparison.

## Relation geometry and homology

Let C be a relation from V to W, let ε ≥ 0, and suppose related points are at distance at most ε.
For any finite target label set τ contained in C(σ), each w ∈ τ has an antecedent
v ∈ σ. At every ambient center z the triangle inequality gives

```
dist(z, q w) ≤ dist(z, p v) + ε ≤ radiusAt(p, z, σ) + ε.
```

Taking the finite maximum gives the radius estimate. Taking infima over centers gives
the same estimate for face values. This step does not require a minimizing center,
so no properness is needed for the radius-filter theorem. For a source closed-ball
face, its existing center witnesses the target closed-ball face directly.

If C and its converse are total on labels, the existing selector-independent relation
maps give canonical ε-interleavings of both homology filtrations, over every ring.
Their composites are the double-shift structure maps. For finite labels and field
coefficients, each radius filter supplies its own critical grid and finite-dimensional
fibers; algebraic stability gives the full-diagram bound. No common critical grid or
essential-multiplicity premise is needed.

For the Hausdorff theorem, take C to consist of pairs at distance at most the Hausdorff
distance of the two ranges. Both ranges are finite and compact, so nearest points
exist and C is total in both directions. This uses compactness of the ranges, rather
than compactness or properness of Z. Configurations with the same range therefore
have equal diagrams, even when their label multiplicities differ.

## Finite samples of an infinite target

For any target A ⊆ Z, write h∞ for extended Hausdorff distance and let α, β be extended
nonnegative error bounds. If finite nonempty
samples p and q satisfy h∞(range p, A) ≤ α and h∞(range q, A) ≤ β, then

```
bottleneck(dgm k (Cech.filter p) n, dgm k (Cech.filter q) n) ≤ α + β.
```

The target may be infinite and has no diagram in this statement. Extended distance
preserves infinite errors, including the empty-versus-nonempty case; real Hausdorff
distance assigns zero when the extended distance is infinite. The real-valued
Hausdorff endpoint consequently requires both finite configurations to be nonempty.

## Public interfaces and source scope

`CechRelation` contains the radius, infimum and shifted-face estimates, along with
`complexFiltration` and its proper-space comparison. `CechRelationInterleaving` contains
the canonical interleavings and finite-diagram relation bound. `CechHausdorff` supplies
`bottleneck_dgm_le_hausdorffDist`, its extended-distance form, the sampling-error sum
and `dgm_eq_of_range_eq`. The fixtures in `CechRelationExamples` include unequal label
counts, a many-to-one collapse, an insufficient displacement budget, an empty pair
and a line configuration whose merging edge moves from radius 1 to 3/2 while its
essential H₀ bar remains born at zero.

[CDSO13-v3](references.md#CDSO13-v3), Lemma 4.9 and Corollary 4.10, supplies the
fixed-witness ambient Čech relation mechanism. The exact closed-ball construction
follows that mechanism. Transfer to an infimum-radius filter, arbitrary ring
coefficients, duplicate labels and the finite full-diagram consumer are proved
library extensions. The negative-time convention is the library's empty tail.
These statements compare configurations inside one ambient space; they give no
intrinsic Čech Gromov–Hausdorff theorem or diagram for a general infinite target.
