# Distance-matrix stability of Rips persistence images

Fix two metrics d,e on the same finite labelled vertex set V, a coefficient field k
and a homological degree n. Use the [diameter-time Rips filtration](rips-metric-stability.md):
vertices enter at zero, thresholds are closed, and stages below zero are empty. Let
D_d,D_e be the diagrams of actual sublevel homology, and write

δ = max { |d(v,w) − e(v,w)| : v,w ∈ V },

with empty maximum zero. The existing actual-diagram theorem bounds their full
bottleneck distance by δ, including their essential bars.

## Finite image and bound

For a positive diagram D, let D_fin be its finite birth–death occurrences and N_D their
number. Each pair satisfies birth < death. Equal pairs keep separate occurrences,
so N_D and every image sum count multiplicity. Define PI_fin(D) by applying the
[existing Gaussian image](persistence-images.md) to D_fin. Essential bars are omitted
from this feature; their deaths are never replaced by finite cutoffs.

Fix the same bandwidth σ > 0, weight w and pixels for both inputs. On the
birth–persistence plane, require 0 ≤ w ≤ B, maximum-norm Lipschitz coefficient A,
and w(b,0)=0, with A,B ≥ 0. Pixels form a finite measurable pairwise disjoint family;
the family may be empty. Set C = 2A + 3B sqrt(2/π)/σ. If N_d,N_e are the finite counts
of D_d,D_e, then

‖PI_fin(D_d) − PI_fin(D_e)‖₁ ≤ C (N_d + N_e) δ.

This explicit nonsharp pixel-vector bound allows different finite-bar counts, changed
pairings, coincident critical values and empty V. Counts are measured on the resulting
diagrams; no bound in terms of the vertex count is assumed. The coefficient is independent
of the number of pixels. No uniform cardinality-free bottleneck estimate is asserted.

## From the matching maximum to the finite sum

More generally, let D,E have finite full bottleneck β. The existing occurrence matching
has a finite partial injection and a separate essential-occurrence bijection. Its type
already forbids finite/essential cross-matches. Keeping the finite map and replacing
the essential types by the empty type preserves every finite charge: one pair or
diagonal charge per source, and one diagonal charge per unmatched target.

Every charge is at most the full matching maximum. There are at most N_D+N_E charges,
so the restricted total cost is at most (N_D+N_E) times that maximum. Empty sums and
maxima are zero. Each individual matching has finite cost because all its occurrence
types are finite and all coordinates, including essential births, are real. This
justifies monotonicity when converting its costs from `ℝ≥0∞` to `ℝ`.

Finite β implies equal essential cardinalities and supplies an attained optimal full
matching through the existing API. Use its restriction as a candidate for the
[finite first-order minimum](finite-first-order-matching.md) m₁. Thus

m₁(D_fin,E_fin) ≤ (N_D+N_E) β.

The finite-bottleneck hypothesis is necessary. A diagram with finite pair (0,2) and
one essential bar, compared with the empty diagram, has full bottleneck `⊤` and finite
first-order cost 1. In Lean, `ENNReal.toReal ⊤ = 0`; an unrestricted real version of
the bound would therefore be false. The Rips bound is below `ENNReal.ofReal δ`, hence
finite, so its consumer needs no extra essential-cardinality hypothesis.

Apply the existing bound ‖PI(x)−PI(y)‖₁ ≤ C m₁(x,y), then the finite-sum comparison
and the Rips bottleneck bound. Positivity of actual diagrams supplies every finite
positive-length hypothesis. Pairing changes require no fixed template.

Multiplicity explains the count factor: m+1 copies of (0,2) against the empty input
have first-order cost m+1 and bottleneck 1. Essential-only diagrams have zero finite
image. These cases and a nonzero two-point metric perturbation exercise the interfaces.

## Interfaces and source scope

`FiniteMatchingCostBottleneck` supplies `OccurrenceMatching.finiteRestriction`, its
sum-to-maximum estimate and `finiteFirstOrderMatchingCost_le_card_mul_bottleneck`.
`PersistenceImageDiagram` supplies `finiteDiagramImage`, its empty-finite-part formula
and count-dependent bottleneck estimate. `RipsPersistenceImage` supplies
`norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy`, with the same `LinearOrder V`,
`Fintype V` and k : Type u field assumptions as the existing Rips API for V : Type u.
Ordinary `TDA.Persistence` includes these noncomputable mathematical APIs.

[Adams et al.](references.md#AE17), §4 Definitions 1–2 and §5 Theorems 9–10, provide
the Gaussian PI construction and first-order stability route. The library's
maximum-norm weight condition and nonsharp C are its proved variant. Remark 6's lack
of a uniform bottleneck constant is consistent with the count factor here.
[Divol–Lacombe corrected v4](references.md#DL20-v4), formulas (1)–(2) and Remark 1.2,
distinguish finite matching costs and essential contributions.
[Chazal–de Silva–Oudot v3](references.md#CDSO13-v3), §4.2.1, supplies the nonnegative-scale
diameter convention; the library retains its stated different negative-time convention.
The finite count comparison and composed Rips-to-PI estimate are library results,
not literal theorems attributed to these papers. Registered versions and rights remain
those in the source register.

Numerical integration, executable distance-matrix reduction, first-order essential
costs, measure-coupling equality, general p, RKHS norms, different-point-set/Gromov–Hausdorff
stability and Čech comparisons require separate results.
