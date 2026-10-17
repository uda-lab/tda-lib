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

| Example | Powered/rooted calculation |
| --- | --- |
| Empty target, diagonal charges 1 and 2, p=2 | Powered optimum 5; rooted optimum √5 |
| Half mass from (0,2) to (0,4), p=2 | Plan cost 9/2; both boundary deficits are 1/2; optimum is 4 |
| Two copies of (0,2) versus one copy, p=2 | Powered and rooted optimum 1, attained by half from each source and by an incidence plan |
| (0,2) versus (3/2,7/2) | p=1 pairs, cost 3/2; p=2 deletes both, powered cost 2, strictly below the paired cost 9/4 |
| (0,8) versus empty, p=3/2 | Powered optimum 8; rooted optimum 4 |

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

[Figalli–Gigli](references.md#FG10) retains priority for boundary-reservoir transport;
its original bounded-domain quadratic Euclidean setting is distinct from this model.
[Divol–Lacombe corrected v4](references.md#DL20-v4), formula (1), separates p from
the ground norm q. This finite occurrence model uses q=∞ and real p≥1. Definition 2.1
and Proposition 3.2 concern measure transport; the latter's finite case invokes
[Lacombe–Cuturi–Oudot](references.md#LCO18-v2), Proposition 1 / Supplement §7.1.
Their displayed convention ties the ground norm to p. Reusing the assignment proof
with maximum-norm powered coefficients is a checked library adaptation, not a
verbatim specialization of that displayed theorem.

The proved equality concerns finite real reservoir matrices, not all Borel/Radon
couplings. Essential or infinite bars, arbitrary weighted inputs, completeness and
barycenters remain outside it. General-p triangle/separation laws and quotient or
metric instances are not supplied. Existing first-order distance laws remain in
[the first-order matching module](finite-first-order-matching.md). The raw augmented
cost is not an ordinary metric obtained by merely collapsing the diagonal.
