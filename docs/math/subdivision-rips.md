# Normalized subdivision-Rips and measure stability

For a nonempty finite metric space `X`, write `R_r(X)` for the complex of
nonempty finite sets whose pairwise distances are strictly less than `2r`.
The vertices of its subdivision are nonempty simplices. A subdivision face is
a finite strict inclusion flag. At mass threshold `k`, retain flags whose
least simplex `σ` satisfies `|σ| / |X| ≥ k`. Decreasing `k` and increasing `r`
give inclusions. Both coordinates remain strictly positive.

`TDA.Filtration.SubdivisionRips.bifiltration` constructs this concrete flag
bifiltration. Flags are represented as finite sets of pairwise comparable
simplices; `mem_subdivision_iff_of_least` identifies the threshold with the
condition on their least member. `mem_openRips_iff_diameter_lt` records the
conversion to the existing diameter convention. Isometric bijections preserve
flag membership, including the carrier-size normalization.
`relabelIso` gives the induced natural isomorphism of homology modules.

`TDA.Persistence.SubdivisionRips.homology` applies the existing simplicial
chain homology in every degree, over every coefficient ring. Its structure
maps are the actual maps induced by flag inclusions. A fixed order on finite
subsets orients the chains independently of the metric and the parameters.
For two metrics on one labelled carrier with distance-matrix discrepancy at
most `2δ`, `metricInterleaving` gives their homology interleaving with shift
`(k,r) ↦ (k−δ,r+δ)`. Its restrictions recover both modules exactly. `pairwiseInterleaving`
constructs this witness directly from two finite metric inputs, choosing half
the maximum distance-matrix discrepancy as the shift.

The interleaving uses the two-copy category of Blumberg–Lesnick,
Definitions 2.32–2.33. Between different copies, an arrow from `(k,r)` to
`(l,s)` exists when `l ≤ k−δ` and `r+δ ≤ s`, with both endpoints in the
positive index. In particular, a source with `k ≤ δ` has no cross arrow.
There is no extension or clamp at mass zero.

`TDA.Topology.MeasureBifiltration.interleavingDiagram` proves the measure-side
statement: if the ambient Lévy–Prokhorov distance of finite measures `μ,ν` is
strictly less than `δ`, their open-ball mass bifiltrations admit that restricted
interleaving. Its maps preserve the ambient center and are continuous subspace inclusions
(`topologicalInterleaving`); its functor laws check
all ordinary and mixed compositions. The proof uses mathlib's measurable-set
Prokhorov inequalities and the triangle inequality for thickenings of balls.
`uniformMeasure_real` identifies a finite uniform pushforward with normalized
counting, including repeated labels.

For a finite metric input, the distance-coordinate map into `X → ℝ`, equipped
with the sup metric, preserves distances. The open Čech complex in this space
is exactly `R_r(X)`. The proof reuses the coordinatewise closed-ball Helly
witness at a radius strictly below `r`, preserving the open boundary.
`distanceCoordinates_cechHomology_eq` identifies the resulting normalized
Čech flag homology diagram with the subdivision-Rips module. This is equality
of whole diagrams and therefore preserves both parameter structure maps.

For finite nonempty metric inputs, `FiniteGromovProkhorov` takes the infimum
of the ambient Lévy–Prokhorov costs of their uniform measures over common
metric spaces and isometric embeddings. Every parameter above this infimum
has an actual ambient witness. Distances to the finitely many points in the
two images embed their joint support into the fixed sup-norm product
`(X ⊕ Y) → ℝ`. `coordinatesAmbient_cost` proves that this replacement preserves
the exact Prokhorov cost, using the finite-uniform cross-distance transport
lemmas. Finite closed subsets of the support suffice to test the cost, as in
`levyProkhorovDist_uniform_le_of_isClosed`, agreeing with the source
closed-set convention. Every such ambient cost therefore gives an upper bound on the same GP
infimum.
`supNormWitness` constructs the resulting finite-dimensional witness and its
actual restricted multicover interleaving.

If an isometric inclusion adds points to a finite uniform sample, then
`gromovProkhorovEDist_embedding_le` proves

`d_GP(X,Y) ≤ (|Y| − |X|) / |Y|`.

The locations of the added points are unrestricted. This follows from the
normalized-count inequality and `levyProkhorovEDist_uniform_embedding_le` in
the enlarged sample's own ambient space. `uniformOutlierInterleaving` gives
the multicover interleaving for each larger shift. The half-mass example adds
one point at any prescribed nonzero distance. The denominator `|Y|` gives a
sharper library bound than the `|X|` denominator displayed in the source
Remark 2.16.

For the next comparison, index a cover by all finite label sets `σ`. Its
member is the common intersection of their radius-`r` open balls when `σ`
is a Čech simplex with `|σ| / |X| ≥ k`, and is empty otherwise.
`stage_uniform_eq_iUnion_largeFaceCover` proves that the union is exactly the
actual multicover stage. The cover is open and increases under both parameter
structure maps. In a real normed ambient every nonempty finite intersection
is contractible. A maximal member of a Čech flag supplies a common center,
giving `subdivision_openCech_le_largeFaceNerve` and the natural morphism
`cechHomologyToLargeFaceNerve` on actual simplicial homology. The same finite
sup-norm GP witness supplies these comparison morphisms for both input SR
modules on the ambient used by its multicover interleaving.

The full Gromov–Prokhorov bound for subdivision-Rips homology remains open.
The flag-to-cover-nerve inclusion is a natural isomorphism on homology:
`cechHomologyToLargeFaceNerve_isIso` proves this at every index and degree over
every ring, comparing the subdivision of a large-face nerve with the flag complex
through face unions and the barycentric homology isomorphism
(`barycentricHomologyIso`). For a sup-norm GP witness at scale δ, near-label
vertex maps between the two large-face covers give
`SupNormWitness.largeFaceNerveHomologyInterleaving` on the restricted two-copy
index, including all mixed composites; transport along the two isomorphisms gives
`SupNormWitness.homologyInterleaving`, whose restrictions are exactly the two
subdivision-Rips homology modules. Hence
`subdivisionRipsHomologyInterleavingDistance_le_gromovProkhorovEDist`: the
restricted homology interleaving distance is at most the finite-uniform GP
distance, for finite nonempty metric spaces in one universe, every ring and every
degree. The comparison stays combinatorial. It does not identify cover-nerve
homology with the homology of the multicover space, exports no homotopy
interleaving, and states no bound for non-uniform measures.

Source: A. J. Blumberg and M. Lesnick, [*Stability of 2-Parameter Persistent
Homology*](https://arxiv.org/pdf/2010.09628), Definitions 2.10–2.15,
2.32–2.33, Remark 2.16, Theorem 3.1, and the finite sup-norm embedding step in the proof of
Theorem 1.6(iii). Theorem 3.3 and its Section 4 proof motivate the flag-to-cover-nerve
comparison; the library proves its homology-level invertibility combinatorially and
does not identify cover-nerve homology with the homology of the multicover space.
