# Closed ambient Čech complexes and the Rips/Čech sandwich

Fix a pseudometric space X and labelled points p : V → X. The label type V carries no
finiteness, decidability or injectivity assumption. Equal points at distinct labels are
distinct vertices.

## Čech complexes

The closed ball family at radius r assigns to each label v the ball
B(p v, r) = {x ∈ X : dist x (p v) ≤ r}. The Čech complex at r is the ordinary nerve of
this family. A finite set s of labels is a face exactly when s is nonempty and some
x ∈ X satisfies dist x (p v) ≤ r for every v ∈ s. Witnesses range over all of X, and the
labelled points are landmarks. Čech time is the ball radius.

Enlarging r enlarges every ball, so the complexes increase with r. A singleton is a face
exactly when r ≥ 0, because a closed ball is nonempty exactly at nonnegative radius.
Below zero every face would need a witness at negative distance, so the complex is empty.

## The sandwich

The Rips convention is the existing diameter-time convention: a nonempty s lies in the
Rips sublevel at r when all pairwise distances, self-pairs included, are at most r.

- **First inclusion.** If all pairwise distances in a nonempty s are at most r, choose
  v₀ ∈ s. The point p v₀ is a Čech witness at radius r.
- **Second inclusion.** If x witnesses s at radius r, then for v, w ∈ s the triangle
  inequality gives dist (p v) (p w) ≤ dist x (p v) + dist x (p w) ≤ 2r.

Both pairwise forms hold for repeated labels. The Rips forms
Rips_r ⊆ Čech_r ⊆ Rips_{2r} take a metric d on V with d(v,w) = dist (p v) (p w) for
all v, w. Such a d exists exactly when p is injective, for instance the induced metric.

## The radius filter

For x ∈ X and a finite s, the radius at x is the largest distance from x to the points of
s, with empty maximum zero. It is at most r exactly when r ≥ 0 and every point of s is
within r of x. It increases with s and is 1-Lipschitz in x, hence continuous.

The Čech value of a nonempty s is the infimum over X of the radius at x. Monotonicity in s
holds pointwise and passes to the infimum, so the values form a filter function on the
full complex of nonempty finite label sets. Every value is nonnegative.

A Čech witness x at radius r gives a radius at most r, so every Čech complex lies in the
sublevel of the radius filter at r. Equality holds when X is proper. Choose v₀ ∈ s and
let R be the radius at p v₀. The closed ball K of radius R about p v₀ is compact, so the
continuous radius attains a minimum on K at some y. A point x outside K has radius at
least dist x (p v₀) > R, which is at least the radius at y. Hence y minimizes globally
and its radius equals the value. A face of value at most r therefore has a Čech witness.

Under the distance-compatibility hypothesis on d, every face s satisfies

rips(s)/2 ≤ čech(s) ≤ rips(s).

The upper bound takes x = p v₀: its radius is at most the diameter. For the lower bound,
the triangle inequality bounds the diameter by twice the radius at every x; X is nonempty
because s has a vertex, so the bound passes to the infimum.

## Fixtures

- **Two points on the line.** For p = (0, 2) in ℝ, the edge is a Čech face at radius 1,
  witnessed by the midpoint, and at no smaller radius. It is absent from the Rips sublevel
  at 1 and present at 2. Its Čech value is exactly 1, half its Rips value, so the lower
  value bound is sharp.
- **An acute triangle.** In the Euclidean plane take (0,0), (2,0) and (1,2), with
  r = 6/5. Every edge is a Čech face, witnessed by its midpoint. The triangle is not:
  for every x,

  5/16·|x−a|² + 5/16·|x−b|² + 3/8·|x−c|² = |x−(1,3/4)|² + 25/16,

  and 25/16 > 36/25. The triangle lies in the Rips sublevel at 12/5, while no edge lies
  in the Rips sublevel at 6/5. Both inclusions are therefore strict on one family.
- **The punctured line.** In {x ∈ ℝ : x ≠ 0} with p = (−1, 1), the closed unit balls
  meet only at the missing origin, so the edge is not a Čech face at 1. Its value is
  exactly 1: the lower value bound gives at least 1, and the witnesses ε > 0 have radius
  1 + ε. The sublevel at 1 is strictly larger than the Čech complex, so the equality
  theorem cannot drop properness.
- **Repeated labels.** Two labels at the point 0 of ℝ form a Čech edge at radius 0 with
  value 0. Only the pairwise forms apply.
- **Negative radius.** For every p the complex at −1 is empty, and no singleton is a face.

## Interfaces

`TDA.Filtration.Cech` defines `ballFamily`, `complex`, `radiusAt` and `filter`. The
complex lemmas are `mem_complex_iff`, `complex_mono`, `singleton_mem_complex_iff` and
`complex_eq_bot_of_neg`. The sandwich is `mem_complex_of_pairwise`,
`dist_le_two_mul_of_mem_complex`, `ripsSublevel_le_complex` and
`complex_le_ripsSublevel_two_mul`. The filter results are `complex_le_sublevel`,
`exists_radiusAt_eq_value`, `sublevel_eq_complex`, `filter_value_le_rips` and
`rips_le_two_mul_filter_value`. The fixtures are in `TDA.Filtration.CechExamples`. These
are noncomputable definitions; no minimal enclosing ball is computed.

## Source correspondence and scope

The closed ambient Čech complex is the complex Čech(L, W; a) of
[Chazal–de Silva–Oudot §4.2.3](references.md#CDSO13-v3) with witnesses W = X and
landmarks labelled by p. Taking X as the point space and p the identity gives the
intrinsic Čech complex of §4.2.2, whose closed balls use the non-strict inequality. The
Rips convention matches §4.2.1. Both definitions are source matches at nonnegative
radii; empty negative stages are the library convention.

The source states no Rips/Čech inclusion. The sandwich, the value bounds and the
proper-space attainment are library extensions. Persistence-level interleavings, homology
of Čech complexes, the Nerve Lemma, open-ball variants and the sharp Euclidean constant
are outside this construction. The
[log-scale Čech–Rips interleaving](cech-rips-interleaving.md) lifts the value sandwich to
homology modules.
