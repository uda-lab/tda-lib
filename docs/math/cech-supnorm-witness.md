# Sup-norm Čech/Rips equality and witness-space change

This note continues the [closed ambient Čech complex](cech-rips-sandwich.md). Fix labels
p : V → X in a pseudometric space X. The face criterion, the radius at a point, the Čech
value and the Rips diameter convention are the ones stated there. The label type V carries
no finiteness, decidability or injectivity assumption.

## Witness-space change

A witness space is a pseudometric space W with a map f : W → X. Labels p : V → W give two
Čech complexes: Čech(p, r) with witnesses in W, and Čech(f ∘ p, r) with witnesses in X.

- **Isometries.** If f is an isometry, the radius at f x for f ∘ p equals the radius at x
  for p, since dist (f x) (f (p v)) = dist x (p v). A witness x ∈ W for a face at radius r
  gives the witness f x ∈ X, so Čech(p, r) ⊆ Čech(f ∘ p, r). For values, a face has a
  vertex v₀, so W is nonempty through p v₀. Every radius over W is a radius over X, and
  the ambient value is at most the value over W.
- **Retractions.** Let g : X → W be 1-Lipschitz with g (f (p v)) = p v for every label.
  For x ∈ X and every label v,

  dist (g x) (p v) = dist (g x) (g (f (p v))) ≤ dist x (f (p v)).

  So an ambient witness x gives the witness g x ∈ W, and the radius at g x for p is at
  most the radius at x for f ∘ p. Hence Čech(f ∘ p, r) ⊆ Čech(p, r), and the value over W
  is at most the ambient value. No isometry hypothesis on f is needed for this direction.
- **Equality.** With an isometry f and such a g, the complexes and values coincide.

For a subset W ⊆ X the map f is the subtype inclusion, which is an isometry. The subspace
complex therefore lies in the ambient one, and its values are at least the ambient
values. The intrinsic complex of q : V → X takes W to be the range of q with labels
corestricted to it; its witnesses are the labelled points themselves. Its composite with
the inclusion is q, so the intrinsic complex lies in the ambient complex.

## The sup-norm product

For a finite index type ι, the space ι → ℝ carries mathlib's sup metric: the distance is
the largest coordinate distance, and zero when ι is empty. This is not the Euclidean
metric of `EuclideanSpace ℝ ι`. Closed balls are axis-parallel boxes.

Let s be a nonempty finite label set whose points are pairwise within 2r. The self-pair
gives 0 ≤ 2r, so r ≥ 0. Put M i for the largest i-th coordinate of a point of s and let
x be the point with coordinates M i − r. For v ∈ s and each coordinate i,

- p v i ≤ M i, so M i − r − p v i ≥ −r;
- for each w ∈ s, p w i − p v i ≤ dist (p w) (p v) ≤ 2r, so M i ≤ p v i + 2r and
  M i − r − p v i ≤ r.

Every coordinate of x is within r of p v, so dist x (p v) ≤ r. This is the
one-dimensional Helly property applied in each coordinate. Combined with the second
sandwich inclusion, s is a Čech face at radius r exactly when s is nonempty and its points
are pairwise within 2r. The criterion holds for arbitrary labels, including repeated
points and empty ι.

For a label metric d with d(v, w) = dist (p v) (p w):

- **Complex equality.** Čech_r = Rips_{2r} for every r.
- **Value identity.** Every face satisfies čech(s) = rips(s)/2. The pairwise distances of
  s are at most rips(s), so the Helly point at radius rips(s)/2 bounds the value from
  above; the lower bound is the merged rips(s) ≤ 2 čech(s). No properness is used.
- **Sublevels and order.** The Čech sublevel at r is the Rips sublevel at 2r, and the
  two filters are ordering-equivalent, since s ↦ rips(s)/2 preserves and reflects every
  weak comparison.

Positive scaling of filters turns these identities into identities of actual diagrams and
bottleneck distances; see [filter and diagram reparametrization](filter-reparametrization.md).

**The line.** For q : V → ℝ, let e x be the constant map Fin 1 → ℝ with value x and let
g y = y 0. Then e is an isometry, g is 1-Lipschitz and g (e x) = x. Witness-space equality
identifies the Čech complexes and values of q with those of e ∘ q. The map e preserves
label distances, so the same d applies, and the sup-norm results for e ∘ q give the
pairwise criterion, the complex equality and the value identity for q.

## Fixtures

- **The sup-norm triangle.** In Fin 2 → ℝ take (0,0), (2,0) and (1,2), the vertices of
  the Euclidean triangle fixture. All pairwise sup distances equal 2. The Helly point at
  radius 1 is (1,1), which witnesses the triangle at radius 1; no smaller radius works.
  The Čech value is 1 and the Rips value is 2. The complex at radius 1 equals the Rips
  sublevel at 2. At radius 6/5 the triangle is a face, while the Euclidean triangle is not.
- **A diagonal pair.** For (0,0) and (2,2) the sup distance is 2. The edge has Čech value
  1, witnessed by (1,1), and Rips value 2.
- **The line read in Fin 1 → ℝ.** For q = (0, 2) and the constant maps q₁ v, every face
  has the same Čech value for q and q₁. The edge value is 1 in both, agreeing with the
  two-point fixture of the merged Čech note.
- **A strictly smaller intrinsic complex.** For q = (0, 2) in ℝ, the edge is an ambient
  face at radius 1 with value 1. Every intrinsic witness is 0 or 2, at distance 2 from the
  other point. The intrinsic edge is absent at radius 1, and its value is exactly 2: the
  upper bound is the Rips value of the induced label metric. Both comparisons are strict.
- **A convex subspace.** For W = [0, 2] with labels 0 and 2, the nearest-point projection
  is 1-Lipschitz and fixes W. The subspace and ambient complexes agree at every radius;
  the edge value in W is 1 and the edge is present at radius 1.
- **Identity control.** The identity is an isometry and a 1-Lipschitz retraction, so the
  equality theorems return Čech(id ∘ p, r) = Čech(p, r).
- **Empty index type.** In Fin 0 → ℝ every nonempty label set is a face at every r ≥ 0.

## Interfaces

`TDA.Filtration.CechWitness` proves `radiusAt_comp_of_isometry`,
`complex_le_complex_comp`, `filter_comp_value_le`,
`complex_comp_le_complex_of_retraction`,
`filter_value_le_filter_comp_value_of_retraction`, `complex_comp_eq_of_retraction`,
`filter_comp_value_eq_of_retraction`, `complex_le_complex_val`, `filter_val_value_le`,
`complex_rangeFactorization_le` and `filter_value_le_filter_rangeFactorization_value`.
`TDA.Filtration.CechSupNorm` defines `supNormWitness` and proves
`dist_supNormWitness_le`, `mem_complex_iff_pairwise`, `filter_value_le_of_pairwise`,
`complex_eq_ripsSublevel_two_mul`, `filter_value_eq_rips_div_two`,
`sublevel_eq_ripsSublevel_two_mul`, `orderingEquivalent_rips` and the line forms
`mem_complex_iff_pairwise_real`, `complex_eq_ripsSublevel_two_mul_real` and
`filter_value_eq_rips_div_two_real`. The fixtures are in
`TDA.Filtration.CechWitnessExamples` and `TDA.Filtration.CechSupNormExamples`.

## Source correspondence and scope

The subspace complex of W ⊆ X is Čech(L, W; a) of
[Chazal–de Silva–Oudot §4.2.3](references.md#CDSO13-v3) with landmarks labelled by p and
witnesses W; the intrinsic complex is the case W = L of §4.2.2. The definitions are source
matches as recorded in the merged Čech note. The comparison theorems between witness sets
are library extensions; no theorem of the paper is exported.

The sup-norm Helly property of boxes and the equality Čech_r = Rips_{2r} in ℓ∞ are
classical. No source for them is registered, and both are library extensions proved
directly. Jung's theorem and Euclidean constants, persistence-level comparisons and
diagram rescaling, Hausdorff and Gromov–Hausdorff stability, including Hausdorff-close
witness sets, the Nerve Lemma, open-ball variants and other product factors are outside
this construction.
