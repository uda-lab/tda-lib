# Metric input and Rips diagram stability

Fix a finite labelled vertex type V and two real-valued metrics d,e on V. The labels
identify the vertices being compared. The metrics are explicit `MetricSpace V` values;
the API does not require two metric instances on V at once.

## Diameter filtration

The full simplex complex contains every nonempty finite subset of V. For a finite
subset s, define

f_d(s) = max {d(v,w) : v,w ∈ s},

with the auxiliary empty maximum equal to zero. The empty set is excluded from the
complex. A singleton has diameter zero, and an edge has value exactly its endpoint
distance. Increasing a face can only increase its diameter.

The diameter values define a `FilterFunction` on this fixed full complex. Its sublevel
at r consists exactly of nonempty s with d(v,w) ≤ r for all v,w ∈ s, including self-pairs.
Thus vertices appear at zero and every stage below zero is empty. This is the closed
Rips filtration with diameter as its time parameter; no ball-radius rescaling is used.

## Perturbation bound

Define the distance-matrix discrepancy

δ = max { |d(v,w) − e(v,w)| : v,w ∈ V },

with δ = 0 when V is empty. For every finite s,

|f_d(s) − f_e(s)| ≤ δ.

Indeed, d(v,w) ≤ e(v,w) + δ ≤ f_e(s) + δ for each pair in s. Taking the maximum,
including its zero seed, gives f_d(s) ≤ f_e(s) + δ. Reversing the metrics proves the
absolute-value estimate. The zero seed also handles s empty without choosing a vertex.

Let dgm_k(f_d,n) be the existing diagram of actual simplicial sublevel homology in
degree n over a field k. The face supremum discrepancy is at most δ, so the existing
finite-face stability theorem gives

bottleneck(dgm_k(f_d,n), dgm_k(f_e,n)) ≤ δ.

In Lean the right side is `ENNReal.ofReal δ`. The theorem uses V : Type u with
`LinearOrder V` and `Fintype V`, and k : Type u with `Field k`, exactly as required by
the existing diagram interface after specializing to a finite carrier. It holds for
every n. It retains occurrence multiplicity, finite interval conventions and essential
deaths at `⊤`; no essential-cardinality or genericity hypothesis is added.

The [finite persistence-image consumer](rips-persistence-images.md) composes this bound
with Gaussian pixel stability and an explicit finite-bar-count factor. Essential bars
remain in the bottleneck comparison and are omitted from the image.

## Interfaces and examples

`TDA.Filtration.Rips` defines `fullComplex`, `diameter`, `filter` and
`pairwiseDiscrepancy`. `mem_sublevel_iff` identifies the closed Rips complex, and
`abs_diameter_sub_le_pairwiseDiscrepancy` supplies the elementary input estimate.
`TDA.Persistence.RipsStability` proves `faceSupDifference_filter_le` and
`bottleneck_dgm_le_pairwiseDiscrepancy`. Ordinary Filtration and Persistence imports
include their respective modules. These are noncomputable mathematical definitions;
they do not provide an executable distance-matrix or point-cloud reduction pipeline.

The example module checks the empty carrier and a singleton, then compares two metrics
on `Fin 2` with off-diagonal distances one and two. Their edge entry times are one and
two, their discrepancy is one, and their actual diagrams satisfy the stated bound in
every degree.

## Source correspondence and scope

The diameter threshold at nonnegative scales matches
[Chazal–de Silva–Oudot §4.2.1](references.md#CDSO13-v3). Section 4.2 defines
correspondence distortion; for the identity relation on a nonempty finite labelled
set, its displayed distance discrepancy has the same formula as δ. This observation
does not introduce a formal correspondence interface.

The source's nonpositive-scale vertex remark is not used here: the support-aware
library convention assigns singleton value zero and empty stages below zero. No full
real-indexed convention equivalence is claimed. The same-label diagram estimate is
independently derived through `bottleneck_dgm_le_faceSupDifference`; it does not
formalize the source's Lemma 4.3 interleaving or Theorem 5.2 Gromov–Hausdorff theorem.
Different vertex sets and Čech comparisons require separate constructions.
