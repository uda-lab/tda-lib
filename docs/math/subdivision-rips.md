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

The full Gromov–Prokhorov bound for subdivision-Rips homology is not yet
proved. The remaining bridge is a natural homology equivalence between the
multicover bifiltration and normalized subdivision-Čech, together with its
compatibility with the restricted interleaving. The finite common-ambient GP
infimum and the outlier-mass GP regression also remain to be connected. No
GP-to-SR distance bound or homotopy interleaving is exported by these modules.

Source: A. J. Blumberg and M. Lesnick, [*Stability of 2-Parameter Persistent
Homology*](https://arxiv.org/pdf/2010.09628), Definitions 2.10–2.13,
2.32–2.33, Theorem 3.1, and the finite sup-norm embedding step in the proof of
Theorem 1.6(iii). The natural multicover nerve theorem is Theorem 3.3; its
proof in Section 4 is outside the results stated here.
