# Finite boundary transport for real matching exponents

Fix a real exponent p ≥ 1. Each input is a finite family of birth–death points,
x : I → ℝ² and y : J → ℝ², with birth < death. Deaths are finite and essential
bars are absent. Labels carry unit mass; equal coordinates with different labels
retain their multiplicity. The ground norm is the maximum norm, independently of p.
Write c(i,j) = ‖x(i) − y(j)‖∞ and δ(z) = |death(z) − birth(z)|/2.

For a partial injection M between the occurrence labels, its powered cost is

Sₚ(M) = Σ matched(i,j) c(i,j)^p + Σ unmatched i δ(x(i))^p
        + Σ unmatched j δ(y(j))^p.

Both unmatched sums are necessary. Set mₚ = min_M Sₚ(M). The all-unmatched
matching exists even for empty inputs, and the finite matching family makes this
minimum attained. The rooted matching quantity is dₚ = mₚ^(1/p). Raising the
first-order minimum to p is a different operation: the optimal matching can change.

## Real plans and their optimum

A `FiniteBoundaryPlan` has real nonnegative entries a(i,j), with every row and
column sum at most one. Its deletion and insertion masses are

u(i) = 1 − Σⱼ a(i,j),    v(j) = 1 − Σᵢ a(i,j).

Its powered transport cost is

Cₚ(a) = Σᵢⱼ a(i,j)c(i,j)^p + Σᵢ u(i)δ(x(i))^p + Σⱼ v(j)δ(y(j))^p.

Distances are powered; mass coefficients stay linear. There is no cardinality or
probability normalization. All fractional real plans satisfying these capacity
conditions are admitted, not just incidence matrices of partial matchings.

The real plan infimum tₚ satisfies

tₚ = inf_a Cₚ(a) = mₚ,    tₚ^(1/p) = dₚ.

Every plan admits an actual partial matching of no greater powered cost. Conversely,
the incidence matrix of an mₚ-minimizing matching attains tₚ. Some optimal plans can
still be fractional. Nonnegativity supplies lower bounds for both real infima; a
zero mass matrix supplies a feasible plan.

At p ≥ 1 the reciprocal-power map is increasing on nonnegative numbers. The
attaining matching and plan therefore also attain the rooted optima, and

dₚ = inf_M Sₚ(M)^(1/p),    tₚ^(1/p) = inf_a Cₚ(a)^(1/p).

These identities use the proved minimizers, without an assumed optimizer or a
claim that taking roots commutes with arbitrary real infima.

## Shared assignment argument

The coefficient-dependent matching cost `OccurrenceMatching.totalBoundaryCost`
and plan cost `FiniteBoundaryPlan.linearCost` take separate pair, deletion and
insertion coefficients. The first-order APIs retain their definitions and types;
their relabelling and assignment proofs reuse these helpers. The powered APIs
supply c^p and δ^p as coefficients.

The augmentation has actual-source rows followed by target dummies, and
actual-target columns followed by source dummies. Every source-row deletion
coefficient is constant over its full dummy block, and every target-column insertion
coefficient is constant over its full block. Dummy-to-dummy cost is zero. Restriction
and completion preserve the three cost sums; completion is a section, not a two-sided
inverse for arbitrary dummy permutations.

Reuse the existing padded mass matrix

D(a) = [[a, diag(u)], [diag(v), transpose(a)]].

After column relabelling it is doubly stochastic, including empty indices.
Mathlib's Birkhoff theorem expresses it as a sum of permutation matrices with
nonnegative coefficients summing to one. The assignment cost is linear in matrix
mass. Each permutation restricts to a genuine matching and costs at least the
finite matching minimum. Their convex average has the same lower bound. This is
the fractional-to-matching argument for both first-order and powered coefficients;
no metric property of the raw boundary blocks is used.

## Empty inputs, labels and compatibility

With y empty, the powered optimum is Σᵢ δ(x(i))^p and its rooted quantity is the
reciprocal-power root of that sum. The analogous target sum applies with x empty.
Both-empty powered and rooted quantities are zero on p ≥ 1. Arbitrary equivalences
of occurrence types preserve every optimum, including repeated coordinates.

At p = 1, candidate matching cost, plan cost, both powered minima and both rooted
quantities agree with their existing first-order APIs. The supporting powered
algebra also permits arbitrary real pairs and exponents; its PD interpretation is
restricted to the domain at the start of this page. In particular, root-infimum
monotonicity and rooted empty-input vanishing are stated with p ≥ 1.

## Rooted distance laws

For a third finite family z : K → ℝ² and every real p ≥ 1, the rooted matching optimum satisfies

dₚ(x,x) = 0,    dₚ(x,y) = dₚ(y,x),    dₚ(x,z) ≤ dₚ(x,y) + dₚ(y,z).

The same laws hold for the rooted finite-real-plan optimum, by its proved equality
with dₚ. On positive-lifetime inputs, zero cost has the precise characterization

dₚ(x,y) = 0 if and only if there is an equivalence e : I ≃ J with x(i) = y(e(i)) for all i.

This preserves values and their multiplicities while allowing different labels.
Unequal raw functions related by a permutation can have zero cost. A diagonal
occurrence has zero deletion cost, so positive lifetimes are needed for this
separation statement. No metric-space instance on raw presentations is supplied.
The self, symmetry and triangle algebra also holds for arbitrary real pairs.

Reversal exchanges the two unmatched parts and preserves the powered paired sum.
For the triangle inequality, compose M from x to y with N from y to z. Let s_M(i)
be M's pair-or-deletion charge at source i, and let t_M(j) be zero at a selected
target j and δ(y(j)) at an unmatched target. Define s_N and t_N analogously.
Place three nonnegative charge families A, B and C on I ⊕ J ⊕ K:

| Index | A | B | C |
| --- | --- | --- | --- |
| Source i | s_M(i) | s_N(j) if M(i)=j, otherwise 0 | s_(M∘N)(i) |
| Middle j | t_M(j) | s_N(j) if M does not select j, otherwise 0 | t_(M∘N)(k) if N(j)=k, otherwise 0 |
| Target k | 0 | t_N(k) | t_N(k) |

Partial injectivity and the selected/complementary partition of J give exact sums

Σ A^p = Sₚ(M),    Σ B^p = Sₚ(N),    Σ C^p = Sₚ(M∘N).

Each input charge occurs once in its own sum. Pointwise C ≤ A+B follows from the
ground triangle inequality and δ(a) ≤ ‖a−b‖∞+δ(b). These cover a middle occurrence
paired on both sides, selected then deleted, and unselected then paired. A middle
occurrence unmatched by both has no endpoint; its two nonnegative input charges
remain unused. N's unmatched targets are also unmatched by the composite.

Monotonicity of positive real powers and finite-sum Minkowski now give

Sₚ(M∘N)^(1/p) ≤ (Σ (A+B)^p)^(1/p) ≤ Sₚ(M)^(1/p) + Sₚ(N)^(1/p).

Choose actual minimizing matchings for the two input costs to obtain the optimum
triangle law. For separation, a sum of nonnegative powered charges is zero
exactly when every raw charge is zero. The existing first-order zero-cost
characterization then supplies the value-preserving equivalence. Conversely,
reindexing a self-matching proves zero cost for such an equivalence.

## Examples

| Example | Powered/rooted calculation |
| --- | --- |
| Empty target, diagonal charges 1 and 2, p=2 | Powered optimum 5; rooted optimum √5 |
| Half mass from (0,2) to (0,4), p=2 | Plan cost 9/2; both boundary deficits are 1/2; optimum is 4 |
| Two copies of (0,2) versus one copy, p=2 | Powered and rooted optimum 1, attained by half from each source and by an incidence plan |
| (0,2) versus (3/2,7/2) | p=1 pairs, cost 3/2; p=2 deletes both, powered cost 2, strictly below the paired cost 9/4 |
| (0,8) versus empty, p=3/2 | Powered optimum 8; rooted optimum 4 |
| Four middle roles with unmatched endpoints, p=2 | Candidate powers 11 and 16; composite power 19; √19 ≤ √11+4 |
| Singletons (0,10), (1,11), (2,12), every p≥1 | Consecutive rooted optima 1 and 1; direct rooted optimum 2; sharp triangle at p=2 and p=3/2 |

The examples also calculate a triangle-inequality failure for the squared optimum:
translating the singleton (0,10) by one twice gives successive squared costs 1 and 1,
but the direct squared optimum is 4. This distinguishes powered sums from metric
claims about rooted quantities.

## API and source scope

`FinitePMatchingCost` supplies powered and rooted matching quantities, attainment,
candidate bounds, root-infimum equality, empty formulas, singleton alternatives,
reindexing and first-order compatibility. `FinitePBoundaryTransport` supplies the
real-plan costs, matching/transport equalities, attaining incidence plans and the
corresponding bounds and formulas. The example module uses these actual definitions.
`FinitePMatchingCostLaws` supplies powered-cost reversal, rooted candidate composition,
the rooted distance laws and positive-lifetime separation.
`FinitePBoundaryTransportLaws` transfers those laws to the actual real-plan optimum.

[Figalli–Gigli](references.md#FG10) retains priority for boundary-reservoir transport;
its original bounded-domain quadratic Euclidean setting is distinct from this model.
[Divol–Lacombe corrected v4](references.md#DL20-v4), formula (1), separates p from
the ground norm q. This finite occurrence model uses q=∞ and real p≥1. Definition 2.1
and Proposition 3.2 concern measure transport; the latter's finite case invokes
[Lacombe–Cuturi–Oudot](references.md#LCO18-v2), Proposition 1 / Supplement §7.1.
Their displayed convention ties the ground norm to p. Reusing the assignment proof
with maximum-norm powered coefficients is a checked library adaptation, not a
verbatim specialization of that displayed theorem.

DL Proposition 3.1 and its Appendix B metric-law proof use boundary gluing and
Minkowski; FG Lemma 2.1 and Theorem 2.2 give the original quadratic antecedent.
The finite occurrence allocation above is checked library reasoning corresponding
to that mechanism. It uses pinned mathlib's `Real.Lp_add_le`, not a measure-gluing
assumption or a triangle law for the raw augmented blocks.

The proved equality concerns finite real reservoir matrices, not all Borel/Radon
couplings. Essential or infinite bars, arbitrary weighted inputs, completeness and
barycenters remain outside it. Quotient and metric-space instances are not supplied.
Existing first-order distance laws remain in
[the first-order matching module](finite-first-order-matching.md). The raw augmented
cost is not an ordinary metric obtained by merely collapsing the diagonal.
