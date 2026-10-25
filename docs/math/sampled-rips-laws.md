# Probability laws of sampled Rips diagrams

An iid tuple `t : Fin n → X` represents the finite metric subspace `Set.range t`.
A point drawn several times appears once in this space. `Rips.sampleDiagram k t q`
is its full degree-`q` Rips diagram over the field `k`. Rips time is diameter:
an edge of length `r` enters at `r`.

For a probability mass function `μ`, `Rips.sampleLaw k μ n q` pushes the iid tuple
law forward through this diagram map. Draws are independent and with replacement.
The outer law has total mass one; the empty diagram is an ordinary possible
outcome. Its mass cannot be discarded at the diagonal.

## Couplings and distortion

`Probability.Coupling μ ν` is a probability mass function on `X × Y` with exact
marginals `μ` and `ν`. It permits arbitrary splitting of mass. On finite input
types this is a nonnegative matrix with prescribed row and column sums.
`Coupling.tuples` draws iid pairs, and `Rips.sampleLawCoupling` pushes these pairs
forward to a coupling of the diagram laws.

For a coupling `π`, the distortion moment is

\[
 A_p(π)=\mathbb E_{a,b\sim π\text{ independently}}
   |d_X(a_X,b_X)-d_Y(a_Y,b_Y)|^p.
\]

`Probability.gromovWasserstein p μ ν` is
`(1/2) inf_π A_p(π)^(1/p)`. The infinity definition uses the essential supremum
on the support of `π` in each independent draw. Zero-mass input points therefore
do not contribute.

`Probability.wasserstein p bottleneck` takes the infimum of the expected powered
bottleneck cost over probability couplings, followed by the `1/p` power. This is
atomic transport between whole diagrams. It is distinct from transporting the
counting measures of their bars.

## Stability estimates

`bottleneck_sampleDiagram_le` proves that a bound on corresponding entries of two
tuple distance matrices bounds their actual sample diagrams. The correspondence
pairs values drawn at the same index, so it allows repetitions and different
numbers of distinct sampled points.

For any input coupling `π`, `transportCost_sampleLaw_le` proves

\[
 \inf_\gamma \mathbb E_\gamma[d_B(D,E)^p]
 \leq {n\choose2}\,A_p(π),\qquad p>0.
\]

The proof bounds the power of the matrix maximum by the sum over unordered pairs
of distinct positions. `expectation_pairEnergy` computes this sum's expectation
exactly as `binom(n,2) A_p(π)`. Taking infima gives
`wasserstein_sampleLaw_le_gromovWasserstein`, for `p ≥ 1`, `n ≥ 2`, and positive
degree `q+1`:

\[
 W_p(\operatorname{sampleLaw}(k,μ,n,q+1),
     \operatorname{sampleLaw}(k,ν,n,q+1))
 \leq 2{n\choose2}^{1/p}\,GW_p(μ,ν).
\]

The separate theorem
`wassersteinInfinity_sampleLaw_le_gromovWassersteinInfinity` proves
`W_∞ ≤ 2 GW_∞`. It uses supported tuples and essential suprema, without a finite-p
limit argument or an assumption that an optimal coupling exists.

## Compact Borel laws

`DiagramBottleneckTopology` equips `Diagram ℝ` with the extended metric induced by
bottleneck distance. Distances may be infinite for diagrams with different
essential-bar multiplicities. Ordered finite-coordinate presentations prove
separability and second countability, so the measurable space is the Borel space
of this topology.

For a compact metric space `X` with Borel probability measure `μ`,
`Rips.sampleLawMeasure k μ n q` is the pushforward of the iid product measure on
`X^n` through the actual finite-sample diagram map. `lipschitzWith_sampleDiagram`
proves its Lipschitz constant is 2, hence it is continuous and measurable. Its
range is compact, and the sampled law assigns that range probability one.
In positive degree, compact diameter bounds the bottleneck distance from every
sample diagram to the empty diagram by twice the diameter of `X`. Consequently
every real power `p > 0` has finite moment from that base diagram.

An isometric embedding preserves the law after pushing forward the input measure.
On a finite input type, `sampleLawMeasure_eq_toMeasure_sampleLaw` identifies the
Borel law of a finite `PMF` with the `toMeasure` of the existing atomic sample law.
For compact-law stability, write `U_{n,q}(μ)` for `sampleLawMeasure k μ n q`, with
one fixed coefficient field `k` and any `q : ℕ`. A probability coupling `π` of
`μ` and `ν` is a measure on `X × Y`
with those exact marginals. In the diameter-time convention used here,
`GW_p(μ,ν)` is one half the infimum over such couplings of the `p`-th root of
the distortion moment integrated against `π ⊗ π`.
For compact Borel probability inputs, the all-degree theorem
`Rips.wasserstein_sampleLawMeasure_le_measureGromovWasserstein_allDegrees`
proves the finite-p bound for the actual probability laws on `Diagram ℝ`, using
`bottleneck` as the ground cost:

\[
 W_p(U_{n,q}(μ),U_{n,q}(ν))
 \le 2{n\choose2}^{1/p}\,GW_p(μ,ν),
 \qquad p\ge1,\ n\ge2,\ q\in\mathbb N.
\]

The proof pushes each input coupling through iid
pair sampling and the Rips diagram maps, bounds its cost, and then takes the
infimum; it does not assume an optimal coupling exists. The positive-degree
wrapper `Rips.wasserstein_sampleLawMeasure_le_measureGromovWasserstein` retains
the specialization to degree `q+1`.

The compact-law infinity theorem
`Rips.wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity_allDegrees`
proves, for every sample size `n` and natural degree `q`,

\[
 W_\infty(U_{n,q}(μ),U_{n,q}(ν))
 \le 2\,GW_\infty(μ,ν).
\]

Here both Wasserstein and Gromov–Wasserstein infinity use essential suprema;
the diagram cost is `bottleneck`, and the input cost is the distortion under
two independent draws from one arbitrary probability coupling. The proof
pushes iid tuples through the sample-law coupling and bounds the diagram
essential supremum by that coupling's distortion essential supremum before
taking the infimum. The factor `2` comes from the one-half GW normalization.
This result assumes no optimal coupling and uses no limit in finite `p`. The
positive-degree wrapper
`Rips.wassersteinInfinity_sampleLawMeasure_le_measureGromovWassersteinInfinity`
retains the specialization to degree `q+1`.
At `q = 0`, both compact-law bounds concern the actual full ordinary H₀ diagrams;
for a nonempty sample they retain the essential `(0,∞)` occurrence. The bounds
do not assert stability for a probability law of reduced H₀ diagrams.

## Scope and remaining bridges

The atomic theorems use probability mass functions and the library's full finite
Rips diagrams. The finite-range projection is surjective and preserves all distances;
`sampleProjection_eq_iff` characterizes its fibers by zero pseudodistance, and
`sampleDiagram_eq_of_range_eq` establishes independence from repeated labels.
`tupleFilter` puts the closed-diameter filtration directly on the tuple indices,
including repeated indices at zero pseudodistance. `mem_tupleFilter_iff` identifies
its faces with the projected Rips faces on the finite metric sample. For any
chosen linear order on that finite sample, `tupleHomologyIso` gives the natural
persistence-module isomorphism in every degree and over every coefficient ring.
The identification of reduced and unreduced positive-degree persistence remains
separate work.

`RipsReducedH0` defines reduced sublevel H₀ as the kernel of the natural
augmentation induced by collapsing each Rips sublevel to a point. On a finite
nonempty metric space, `reducedSublevelH0Diagram_points_eq_finitePart` identifies
the reduced diagram points with the finite part of the ordinary H₀ diagram;
`reducedSublevelH0Diagram_points_eq_eraseEssential` proves this removes exactly
one `(0, ⊤)` occurrence while preserving all other multiplicities.

The compact Borel theorems use the independent `MeasureCoupling` transport
definition directly on whole diagrams. They do not yet identify that transport
infimum with the existing finite-PMF transport cost on finite support, and the
finite-space reduced-H₀ bridge does not supply a reduced-diagram probability-law
bound. The compact bounds above apply to full diagrams, including full H₀ at
degree zero.

## Why the whole support diagram is different

Consider the real-valued two-point law on `0` and `1` with masses `1−ε` and `ε`.
Against a singleton, its distortion moment is `2ε(1−ε)`, so the finite-p
distortion GW distance is `(1/2)(2ε(1−ε))^(1/p)`. The Lean regression proves
that both real-law atoms are positive for `0 < ε < 1`. It also uses the finite
Bool metric chart induced by the same coordinates `false ↦ 0`, `true ↦ 1`:
`epsilonTwoPoint_fullH0_points` gives its full H₀ diagram, with an essential
component and a finite bar `(0,1)`, and
`epsilonTwoPoint_bottleneck_singleton` proves the chart's diagram is exactly
bottleneck distance `1/2` from the one-point diagram. Thus the whole-support
diagram stays nontrivial even as the rare atom's mass tends to zero.

The exact sample-law regression is first stated on that Bool metric chart with
`twoPointWeights`. For `n = 2`,
`epsilonTwoPoint_sampleLaw_nontrivial_mass` proves that the atom at the diagram
with the finite H₀ bar has mass exactly `2ε(1−ε)`, and
`epsilonTwoPoint_sampleLaw_nontrivial_mass_tendsto_zero` proves this mass tends
to zero as `ε → 0`. The reusable `sampleLaw_map_isometry` theorem transports the
full diagram law through an isometric embedding; its specialization
`epsilonTwoPoint_realSampleLaw_nontrivial_mass` proves the same exact atom for
the actual real-valued `twoPointLaw`. This transports the entire law for any
sample size, but the explicit rare-atom formula here is for `n = 2`; no
arbitrary-`n` atom formula is asserted. The full-support diagram therefore
cannot replace the sampled diagram law.

The singleton distortion identity is exposed as
`gromovWasserstein_of_subsingleton`. A separate uniform two-point fixture at
distance two proves that distinct draws have one essential and one finite full
H₀ occurrence, while repeated draws retain only the essential occurrence.
Each of these distinct diagrams receives at least half of the two-draw law's
probability. `uniformTwoPoints_sampleLaw_nonconstant` therefore witnesses a
nonconstant pushforward law with positive mass at both outputs. The ε-dependent
full-support diagram, bottleneck obstruction, exact two-draw atom and
vanishing-mass limit are formalized on the Bool metric chart described above.

## Sources and reuse

The source is Gómez and Mémoli, *Curvature Sets Over Persistence Diagrams*,
[arXiv:2103.04470v5](https://arxiv.org/abs/2103.04470v5), Definitions 2.9–2.10 and
3.18, Theorems 3.8 and 3.19. The finite-p estimate combines their distance-matrix
bound with Rips' diameter-scale Lipschitz constant two. The atomic and compact
Borel probability-law bounds use full finite sample diagrams. The compact Borel
bounds apply in every degree; at degree zero they are laws of full ordinary H₀
diagrams. The separate finite Rips reduced-H₀ diagram correspondence is pointwise
and does not assert compact reduced-law stability.

Pinned mathlib supplies probability mass functions, their monad laws, and
extended-real sums and powers. TauCeti's
[`OptimalTransport/Coupling`](https://github.com/TauCetiProject/TauCeti/blob/b971ef7017efd17b28899a41289f2f11cdced2a2/TauCeti/MeasureTheory/OptimalTransport/Coupling.lean)
and [`GromovWasserstein/Finite`](https://github.com/TauCetiProject/TauCeti/blob/b971ef7017efd17b28899a41289f2f11cdced2a2/TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/Finite.lean)
provide related measure-coupling and matrix-objective APIs. Their inspected
revision uses a different Lean toolchain and a GW convention without the factor
one half; no TauCeti code or dependency is imported here.
