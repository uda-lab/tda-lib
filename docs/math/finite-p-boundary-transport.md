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

Every plan admits a partial matching of no greater powered cost. Conversely,
the incidence matrix of a mₚ-minimizing matching attains tₚ. Some optimal plans can
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

The augmentation has source-occurrence rows followed by target dummies, and
target-occurrence columns followed by source dummies. Every source-row deletion
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
For the triangle inequality, follow M from x to y by N from y to z. Let s_M(i)
be M's pair-or-deletion charge at source i, and let t_M(j) be zero at a selected
target j and δ(y(j)) at an unmatched target. Define s_N and t_N analogously.
Use the disjoint union of source, middle and target labels, written I ⊕ J ⊕ K,
as a common index for three nonnegative charge families A, B and C:

| Index | A | B | C |
| --- | --- | --- | --- |
| Source i | s_M(i) | s_N(j) if M(i)=j, otherwise 0 | s_(N∘M)(i) |
| Middle j | t_M(j) | s_N(j) if M does not select j, otherwise 0 | t_(N∘M)(k) if N(j)=k, otherwise 0 |
| Target k | 0 | t_N(k) | t_N(k) |

Partial injectivity and the selected/complementary partition of J give exact sums

Σ A^p = Sₚ(M),    Σ B^p = Sₚ(N),    Σ C^p = Sₚ(N∘M).

Each input charge occurs once in its own sum. Pointwise C ≤ A+B follows from the
ground triangle inequality and δ(a) ≤ ‖a−b‖∞+δ(b). These cover a middle occurrence
paired on both sides, selected then deleted, and unselected then paired. A middle
occurrence unmatched by both has no endpoint; its two nonnegative input charges
remain unused. N's unmatched targets are also unmatched by the composite.

Monotonicity of positive real powers and finite-sum Minkowski now give

Sₚ(N∘M)^(1/p) ≤ (Σ (A+B)^p)^(1/p) ≤ Sₚ(M)^(1/p) + Sₚ(N)^(1/p).

Choose minimizing matchings for the two input costs to obtain the optimum
triangle law. For separation, a sum of nonnegative powered charges is zero
exactly when every raw charge is zero. The existing first-order zero-cost
characterization then supplies the value-preserving equivalence. Conversely,
reindexing a self-matching proves zero cost for such an equivalence.

## Comparison with first-order distance

Let N = card I + card J count both occurrence families. For every real p ≥ 1,
the unnormalized matching distances satisfy

dₚ(x,y) ≤ d₁(x,y) ≤ N^(1−1/p) dₚ(x,y).

The same comparison holds for the rooted finite-real-plan optima, by
their equality with the matching optima. Empty families are included: if N=0,
all distances are zero. At p=1 the factor is one and both inequalities are equalities.

For a matching M, form a nonnegative charge vector on I ⊕ J. At a source label,
use its pair cost if selected and its deletion cost otherwise. At a target label,
use zero if selected and its insertion cost otherwise. Its sum is S₁(M), and
the sum of its p-th powers is Sₚ(M). Each paired cost occurs once; both unmatched
parts remain. Finite-sum power inequalities give

Sₚ(M)^(1/p) ≤ S₁(M) ≤ N^(1−1/p) Sₚ(M)^(1/p).

For the first optimum inequality choose a first-order minimizing matching. For
the second choose a p-minimizing matching. Both exist, including for empty inputs;
one matching need not minimize both exponents. The algebra also applies to raw
real pairs without positive lifetimes.

Two copies of (0,2) versus empty have d₁=2 and dₚ=2^(1/p), attaining the upper
factor. At p=3/2 these are 2 and 2^(2/3), with factor 2^(1/3).
The comparison is about optimized plans. A fractional candidate sending mass
3/4 between identical bars (0,2) has C₁=C₂=1/2, so its rooted second-order cost
exceeds its first-order cost even though their common optimum is zero.

## Comparison at two real exponents

For real 1 ≤ r ≤ s and the same occurrence count N,

dₛ(x,y) ≤ dᵣ(x,y) ≤ N^(1/r−1/s) dₛ(x,y).

Both inequalities also hold for the rooted real-plan optima. Thus each
optimized distance is antitone on [1,∞), with the maximum ground norm fixed.
The families may be empty and distances may vanish. At r=s the factor is one,
including 0^0=1 when N=0.

For the matching charge vector a, apply the preceding finite-sum inequalities
to the vector with entries a_k^r at exponent s/r, then raise both sides to 1/r.
Nonnegative-base power identities give the displayed factor without dividing by N. To pass to optima,
choose an r-minimizer for the lower comparison and an s-minimizer for the upper
comparison. Equality of matching and real-plan optima transfers the result to
all feasible real reservoir matrices after optimization.

Two labelled copies of (0,2) versus empty attain the upper bound: their rooted
costs at r=3/2 and s=3 are 2^(2/3) and 2^(1/3), with factor 2^(1/3).
For the singletons (0,2) and (3/2,7/2), the optimum changes from pairing at
exponent one, with cost 3/2, to deleting both at exponent two, with rooted
cost √2. The comparison does not require a common optimizer.

Candidate plans need not be antitone. Sending half a unit from (0,2) to (6,8)
and leaving half a unit at each boundary has powered costs 4 and 19 at exponents
one and two. Its rooted second cost √19 exceeds 4, while the optimized
distances are 2 and √2 and satisfy the comparison.

## Continuity at finite exponents

Fix the two occurrence families. The four functions p ↦ mₚ, p ↦ dₚ,
p ↦ tₚ and p ↦ tₚ^(1/p) are continuous on [1,∞). Empty families,
nonempty zero-distance inputs and repeated coordinates are included. The
statement concerns the optimized values even when their minimizing matchings
change with p.

For a fixed matching, each branch of the source and target sums is fixed as p
varies. Powers of its nonnegative geometric coefficients are continuous at
positive exponents, including zero coefficients. A finite nonempty minimum of
these continuous candidate functions is continuous. The proof identifies this
finite minimum with the existing real infimum; it does not interchange a limit
with an arbitrary infimum. The reciprocal exponent is positive, so rooting is
continuous even when mₚ=0. The proved assignment equalities transfer the result
to the infimum over all feasible real plans.

Identical singleton bars have zero optimized cost throughout the domain, while
two labelled copies of (0,2) versus empty have powered cost 2 and rooted cost
2^(1/p), in either orientation. For (0,2) versus (3/2,7/2), the powered curve is
min((3/2)^p,2). It remains continuous as the optimizer changes from pairing to
deleting both.

Exponent zero lies outside this domain. Under the existing real-power
conventions, the empty rooted cost is 1 at zero and 0 at every positive exponent.
For identical singleton bars (0,2), the powered optimum is also 1 at zero and 0
at positive exponents. These positive-side limits differ from the values at zero.
The continuity API keeps the definitions and the PH exponent domain unchanged.

## Joint continuity with moving coordinates

Keep the finite occurrence types I and J fixed, and give their coordinate
families the ordinary function-space topology. On
ℝ × ((I → ℝ²) × (J → ℝ²)), restricted to p ≥ 1, the four optimized values
mₚ(x,y), dₚ(x,y), tₚ(x,y) and tₚ(x,y)^(1/p) are jointly continuous.
Consequently, a continuous parameter family a ↦ (p(a),x(a),y(a)) with p(a) ≥ 1
has continuous optimized costs. Both families and the exponent may move together.

For a fixed matching, pair coefficients are maxima of absolute coordinate
differences, and boundary coefficients are half the absolute lifetime. These
are continuous real functions. Joint continuity of real powers at positive
exponents includes zero coefficients. Both unmatched sums remain, and their
branch choices depend only on the fixed matching. Taking the finite nonempty
minimum, then its positive reciprocal power, preserves continuity even at a
zero minimum. The assignment equalities again transfer the result to all
feasible real reservoir matrices.

For example, let p(t)=1+t² and take singleton families x(t)=(t,t+2) and
y(t)=(-t,2-t). Both bars have lifetime 2, and their powered optimum is
min((2|t|)^(1+t²),2). All four optimized path costs are continuous. At t=0 they
vanish; at t=1/2 pairing costs 1 while deleting both costs 2; at t=1 pairing
costs 4 while deleting both still costs 2. Thus the result includes a change of
minimizing matching with both coordinates and exponent moving.

The examples also vary the lifetime of two repeated labels in both one-empty
orientations. A raw singleton (t,-t) versus empty has rooted cost |t|, continuous
through its diagonal collision at zero. It is a positive bar for t<0 and lies
below the diagonal for t>0. The diagonal and below-diagonal cases exercise the
raw cost algebra.
Fixed label types and cardinalities are part of the joint domain. This finite
library derivation introduces no topology on changing presentations or general
persistence measures. The exponent-zero discontinuities above still apply:
identical singleton bars (q,q+2) have powered optimum 1 at exponent q=0 and
optimum 0 for q>0, even as their coordinates move.

## Diagonal translation and nonnegative scaling

Fix p ≥ 1 and use mₚ and dₚ on raw real coordinate families, which permit diagonal
outputs. This makes the zero-scale case meaningful as a cost identity.
For a real t, let Tₜ(b,d) = (b+t,d+t). For a ≥ 0, let Sₐ(b,d) = (ab,ad).
Apply the same map to both input families. Their powered minima and rooted
distances satisfy

mₚ(Tₜx,Tₜy) = mₚ(x,y),    dₚ(Tₜx,Tₜy) = dₚ(x,y),

mₚ(Sₐx,Sₐy) = a^p mₚ(x,y),    dₚ(Sₐx,Sₐy) = a dₚ(x,y).

The finite real-plan optima satisfy the same laws by their equality with the
matching minima. A diagonal shift cancels in every pair and boundary distance.
Scaling multiplies each powered coefficient by a^p, so it multiplies every
matching's sum by that factor. Attained minimizers give both inequalities for
the minimum, including when a=0; no division by a is needed. Taking the
nonnegative reciprocal-power root gives the rooted scaling law.

Every real diagonal shift preserves birth < death, including shifts to negative
births. Applications imposing nonnegative births must separately preserve that
extra condition. Positive scaling preserves positive lifetimes. At scale zero,
the raw coordinate families consist of diagonal points and all costs vanish.
This case belongs to the raw-cost API; `Diagram.scale` still requires a positive
factor. Repeated coordinates retain their occurrence labels throughout.

The shift must be along the diagonal. For example, the first-order distance from
the singleton (0,2) to the empty family is 1; translating vertically to (0,4)
changes it to 2, although both lifetimes are positive. These laws are direct
library derivations from the cost definitions at fixed maximum ground norm.

## Finite-part perturbation bounds

Let D and E be library diagrams and let N be the sum of their finite occurrence
counts. Write B for their full bottleneck distance, mₚᶠⁱⁿ for the powered matching
minimum on their finite occurrence coordinate functions, and dₚᶠⁱⁿ for its root.
This root is also the rooted finite-real-plan optimum by the equality above. Essential occurrences
are excluded from this transport cost and from N, even if D and E contain them.
Assume B is finite. For real p≥1,

mₚᶠⁱⁿ ≤ N B^p,    dₚᶠⁱⁿ ≤ N^(1/p) B.

Choose a full matching attaining B and retain its finite partial injection.
Each finite source contributes a pair or deletion charge at most B. Each target
contributes zero when selected and a boundary charge at most B otherwise. Summing
their p-th powers gives at most N B^p; the finite powered minimum is no larger than
this candidate. This uses a bottleneck optimizer as an upper-bound witness, without
asserting that it also minimizes the p-cost. Nonnegativity, p≠0 and real-power
factorization give the rooted estimate, including N=0 and B=0. Equality with the
real-plan optimum transfers this to the infimum over all feasible matrices.

More generally, if N≤m for a natural cardinality budget m and 0≤r with B≤r, then

dₚᶠⁱⁿ ≤ m^(1/p) r.

A uniform family estimate requires this budget explicitly. Cardinality need not
remain constant under perturbations: bars can reach the diagonal and disappear.
Finiteness of B is also material. In the Lean API an extended infinite value converts
to real zero; essential-cardinality mismatch can make B infinite while the finite-part
transport cost is positive.

For two face filters f,g on the same finite complex, let Δ be the maximum absolute
change of their face values, with Δ=0 for an empty face set. Over the coefficient
field and ordered-vertex assumptions of the degree-n sublevel diagrams,
put D=dgm(f,n) and E=dgm(g,n), and let N(f,g,n) count their finite occurrences on both sides.
The proved full-diagram bottleneck stability gives B≤Δ and hence

dₚᶠⁱⁿ(dgm(f,n),dgm(g,n)) ≤ N(f,g,n)^(1/p) Δ.

The cardinality-budget version replaces N(f,g,n) by any explicit upper bound m.
The existing bottleneck argument allows the barcode pairing and compatible face
order to change; no fixed pairing or order is required here. Essential bars in
these diagrams still belong to the full bottleneck comparison and remain
outside the finite-part transport quantity.

## Limit as the matching exponent tends to infinity

Fix two finite diagrams D,E with empty essential parts. Let B be their full
bottleneck distance and let N count both finite occurrence families. Empty
essential parts imply B<∞, so its real value is meaningful. For every real p≥1,

B ≤ dₚ(D,E) ≤ N^(1/p) B.

Here dₚ uses the canonical finite occurrence labels of D,E. Each charge of a
matching is at most its rooted powered sum. Choose a minimizing finite matching
and extend it by the unique matching of empty essential families. Its maximum
bounds B from above, giving the lower comparison. The upper comparison is the
occurrence-count bound above. Both comparisons concern optimized quantities;
the minimizing matching may change with p.

If N>0, then N^(1/p) tends to one as real p tends to infinity. Squeezing gives

lim_(p→∞) dₚ(D,E) = B.

If N=0, both finite families are empty and both sides are zero; no limit claim
about 0^(1/p) is used. The exact matching/plan identity gives the same limit for
the rooted real boundary-reservoir optimum. The API provides real limits and
extended nonnegative real limits, with B's finiteness proved before conversion.

The comparison can fail for unequal essential births. Essential-only diagrams
with births 0 and 1 have zero finite-part transport at every p≥1, but full
bottleneck one. Finiteness of B alone therefore does not suffice. The common
essential-birth multiset condition below gives another sufficient case.

## Uniform recovery under count and radius bounds

Let m be a natural number and R≥0. Consider all pairs D,E with empty essential
parts, total finite occurrence count N≤m, and bottleneck B≤R. Set M=max(1,m).
For either optimized rooted cost and every real p≥1,

|dₚ(D,E) − B| ≤ (M^(1/p) − 1) R.

Indeed, B≤dₚ≤N^(1/p)B≤M^(1/p)B. Subtract B before using the radius bound:
the error is at most (M^(1/p)−1)B, and this is at most (M^(1/p)−1)R.
Since M≥1, its reciprocal-power factor tends to one. The common error envelope
therefore tends to zero. The API gives `TendstoUniformlyOn` in real p along
`atTop`: one exponent threshold works for every pair in this budget class,
even when its occurrence types and minimizing matchings vary. This needs no
topology or compactness of the set of diagrams. Empty inputs satisfy m=0;
identical nonempty positive diagrams also lie in a zero-radius class.

For R>0, two copies of (0,2R) versus empty have B=R and rooted cost
2^(1/p)R. They attain the budget-two error bound, including p=3/2.
The singleton pair (0,2), (3/2,7/2) belongs to the same count-two, radius-one
class while its optimizer changes from pairing at one to deleting both at two.

Both budgets matter. At exponent n≥1, take 2^n copies of (0,2) versus empty.
Their bottleneck is one and their rooted costs are two, so the error
stays one along cofinal real exponents without a count cap. With count two
fixed, choose a(p)=(2^(1/p)−1)⁻¹>0 and two copies of (0,2a(p)) versus empty.
Their error is one for every p≥1 without a common radius bound. These examples
obstruct a uniform epsilon-one-half tail on the corresponding larger classes;
each fixed pair still has the pointwise limit above. The essential-birth
example also excludes removing the empty-essential hypotheses.

This uniform estimate is a finite library derivation using the DL matching
convention and the existing optimized bounds. The probability-measure theorem
[`TauCeti.tendsto_wassersteinEDist_atTop`](https://github.com/TauCetiProject/TauCeti/blob/5283b03c90ba08f975b65098ee412a890b567a6e/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Infinity/Basic.lean)
is a related pointwise result: its normalized costs increase to their supremum,
using compactness of couplings. These unit-occurrence costs approach bottleneck
from above. The count/radius uniformity here concerns finite essential-free
diagrams; it gives no uniform all-Radon or powered-cost convergence theorem.

## Common essential-birth multisets

The same error bound and uniform limit hold when the entire essential-birth
multisets agree. Equality includes values and multiplicities; the common
multiset may vary across pairs, with no bound on its count or birth values.
Keep the total finite count N≤m and full bottleneck B≤R≥0. For both existing
rooted optima and every real p≥1,

    |dₚ−B| ≤ ((max(1,m))^(1/p)−1)R.

The uniform domain is the literal set of pairs satisfying those three
conditions. One exponent tail works for every pair in it, including m=0 and
R=0. There is no topology on diagrams or chosen common optimizer.

The canonical essential occurrence equivalence preserves each birth value,
including repeated births. Extend a minimizing finite matching by that
equivalence. Its essential charges vanish, so its full maximum equals the
cost of the same finite matching with empty essential types. The existing
rooted-sum bound gives the lower comparison; the arbitrary-essential finite
upper bound gives the same count factor. Equality of essential cardinalities
first establishes full bottleneck finiteness before conversion to real.
optimized real plans use the proved matching equality after optimization.

For example, reordered essential births [-3,-3,7] have full bottleneck and
both finite costs zero. Any number of identical common births, at any real
value, lies in the same zero-budget class. Adding two copies of (0,2R), R>0,
on one side gives B=R and dₚ=2^(1/p)R, attaining the error envelope while
retaining the essential block. Adding that block to (0,2) and (3/2,7/2)
retains the change from pairing at p=1 to deletion at p=2. Essential births
0 and 1 have equal counts but full B=1 and finite costs zero, so cardinality
alone cannot replace multiset equality. Unequal counts give B=∞ and exclude
every finite-radius class.

This is an extension of the existing library model, with no essential p-cost.
DL corrected v4 §1.1, Remark 1.2, describes a sum of independent finite and
essential terms; this library's full bottleneck uses a maximum. Common
essential values give zero essential displacement in either convention.
No identification of general essential metrics or source uniform theorem is
claimed. The essential-free class is a checked restriction of this domain.

## Čech sublevel diagrams under a displacement budget

Fix a finite linearly ordered label type V, a coefficient field k in the same
universe, and a pseudometric ambient space X in an independent universe. A cloud
is an arbitrary function a : V → X; repeated points and empty labels are allowed.
Write D(a) for the diagram `dgm k (Cech.filter a) n`. The filter uses the
infimal enclosing radius over all ambient centers. Its sublevels contain the
closed-ball Čech nerves, and equal them under the existing proper-space
specialization. Attainment is not assumed for the results here.

For n≥1, each D(a) has empty essential part. In degree zero, nonempty labels
give exactly the essential-birth multiset {0}; empty labels give the empty
diagram without choosing an ambient point. Thus the entire essential
multisets of D(a) and D(b) agree in every natural degree. Each diagram has at
most choose(card V,n+2) finite occurrences, and same-label displacement δ(a,b)
bounds the full bottleneck B(a,b). If δ(a,b)≤R with R≥0, put
M=max(1,2 choose(card V,n+2)). For each
optimized rooted cost and every real p≥1,

|dₚ(D(a),D(b)) − B(a,b)| ≤ (M^(1/p) − 1) R.

Both rooted costs converge uniformly to B on the literal cloud-pair class
δ(a,b)≤R as real p tends to infinity. The fixed data are V,k,X,n,R; the exponent
tail precedes every cloud pair in that class. The proof derives the diagram
budgets, precomposes the generic uniform result with (a,b)↦(D(a),D(b)), and
restricts to the displacement class. No topology on clouds or diagrams, fixed
barcode length or common optimizing matching is required.

For labels (0,0),(2,0),(1,2) versus (0,0),(2,0),(2,2) in the Euclidean plane,
the degree-one diagrams over ZMod 2 are the singleton (√5/2,5/4) and
the empty diagram. Displacement is exactly one; B and both rooted optima are
r=(5/4−√5/2)/2>0 for every p≥1. This tests nonzero quantities, including p=2
and p=3/2; its error is zero and does not attain the coarse budget-two rate.
The acute triangle paired with itself tests radius zero with a retained bar.
Empty and repeated-label examples also instantiate the two models.

This is a finite library composition using the DL matching convention. The
[same-label Čech stability argument](cech-displacement-stability.md) supplies its
geometric input; its [CDSO Hausdorff comparison](cech-displacement-stability.md#source-correspondence-and-scope)
and the [radius-filter attainment distinction](cech-rips-sandwich.md#the-radius-filter)
have separate scopes. No uniform p-limit is attributed to that source.

The birth-zero proof uses a vertex at time zero whose inclusion into
a full late stage has nonzero homology range. The diagram-rank formula gives
a point alive between those stages. Every finite death is a critical face
value at most that late time, so this point is essential. Its birth is at
most zero and is a nonnegative critical value, hence zero. Only then does the
essential count one identify the full multiset. An eventual count alone
would not determine the birth.

This ordinary H₀ calculation uses the radius filter's empty negative tail.
CDSO retains vertices at nonpositive scales, so no whole real-indexed H₀
module identification is asserted. The proper-ambient closed-nerve
specialization here is at nonnegative radius. Translating a singleton's
filter values by one gives an essential birth at one, finite costs zero and
full bottleneck one against the original diagram; equal essential counts
alone remain insufficient. The H₀ log module still has no finite-grid zero
left tail. The all-degree real-parameter consumers do not change that fact.

For the clouds (0,2) and (0,6), the H₀ finite bars are (0,1) and
(0,3), with a common essential birth zero. Displacement is four, while full
bottleneck is 3/2. Both rooted finite optima are two at exponent one and
√(5/2) at exponent two: pairing is optimal at one, and deleting both is
strictly better at two. The exponent-one error is 1/2. Comparing the acute
triangle with a constant cloud gives two finite deletions with charges
1/2 and √5/4; repeated labels (0,0,2) give only the positive bar (0,1),
since the simultaneous zero-length merge is filtered out.

## Examples

| Example | Powered/rooted calculation |
| --- | --- |
| Both diagrams empty, every p≥1 | Both optimized costs and bottleneck are zero; the limit includes N=0 |
| One bar (0,2) versus empty, every p≥1 | Both rooted optima and bottleneck are one |
| Empty target, diagonal charges 1 and 2, p=2 | Powered optimum 5; rooted optimum √5 |
| Half mass from (0,2) to (0,4), p=2 | Plan cost 9/2; both boundary deficits are 1/2; optimum is 4 |
| Two copies of (0,2) versus one copy, every p≥1 | Rooted optimum and bottleneck are one, with a pair-one/delete-one matching |
| (0,2) versus (3/2,7/2) | p=1 pairs, cost 3/2; p=2 deletes both, powered cost 2, strictly below the paired cost 9/4 |
| (0,8) versus empty, p=3/2 | Powered optimum 8; rooted optimum 4 |
| Two copies of (0,2) versus empty, any p≥1 | Powered optimum 2; rooted optimum 2^(1/p); bottleneck 1, attaining the occurrence-count factor |
| Essential-only births 0 versus 1, every p≥1 | Finite-part cost zero, full bottleneck one; equal essential counts do not suffice for recovery |
| Two bars (0,2R) versus none, with common essential births [-3,-3,7], R>0 | Full bottleneck R; both rooted optima 2^(1/p)R; the count-two error bound is attained |
| filled triangle versus its tied filter, H₁ | The finite parts have one bar and zero bars; their transport is bounded by the face perturbation, including p=2 and p=3/2 |
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
corresponding bounds and formulas. The example module uses these definitions.
`FinitePMatchingCostLaws` supplies powered-cost reversal, rooted candidate composition,
the rooted distance laws and positive-lifetime separation.
`FinitePBoundaryTransportLaws` transfers those laws to the real-plan optimum.
`FinitePMatchingCostBottleneck` supplies the powered and rooted occurrence-count
bounds, finite radius and cardinality-budget forms. `FinitePFilterStability` applies
them to the finite parts of sublevel diagrams.
`FinitePMatchingCostComparison` supplies first-order and two-real-exponent
comparisons for matching and real-plan optima, including empty occurrence
families, and their antitonicity on [1,∞).
`FinitePCostContinuity` supplies continuity in the real exponent on [1,∞)
for the powered and rooted matching and real-plan optima.
`FinitePCostSimilarity` supplies common diagonal-translation invariance and
nonnegative scaling for powered and rooted matching and real-plan optima.
`FinitePBottleneckLimit` supplies the lower bottleneck comparison and real-exponent
limits for matching and real-plan optima on diagrams with empty essential parts.
`FinitePBottleneckUniformLimit` supplies the common absolute-error bound and
uniform convergence on essential-free count/radius budget classes for both optima.
`FinitePCommonEssentialBottleneck` supplies the same error and uniform conclusions
when the essential-birth multisets agree, without essential count or range bounds.
`CechFinitePBottleneckUniformLimit` derives both bounds and uniform limits for
positive-degree Čech sublevel diagrams from a same-label displacement budget.
`CechEssentialBirth` proves the degree-zero essential multiset, and
`CechFinitePBottleneckAllDegrees` derives both bounds and uniform limits for
every natural degree from the same input budget.

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

The exponent comparisons are finite library derivations from DL formula (1)
and pinned mathlib's power inequalities, rather than theorems quoted from DL.
They use `Real.add_rpow_le_rpow_add` and
`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg` on the matching charge vector.
Probability-normalized Wasserstein exponent comparisons concern a different
normalization and do not supply these unnormalized occurrence bounds.

Finite-exponent continuity is also a finite library derivation using the same
DL convention. Pinned mathlib's finite-infimum identity and continuity theorem
apply to the finite matching family; its real-power continuity includes zero
bases at positive exponents. No continuity theorem for infinite diagrams or
general persistence measures is inferred from this finite-minimum proof.

The perturbation estimates are checked finite sum-to-maximum reasoning from
DL formulas (1)/(2) and the existing bottleneck attainment and stability theorems.
DL Remarks 1.1/1.2 distinguish unstable point counts and the separate essential term.
The formula conventions are compared on finite diagrams. Allowing essential points
on the right of the bound is a one-sided library statement about the finite projection,
not an identification of full essential p-transport conventions.
The arbitrary-real-pair supporting algebra is a library extension; no all-measure
stability theorem is inferred from this count estimate.

The exponent limit is a checked finite-diagram specialization of DL §1.1
formulas (1)/(2), at fixed q=∞. Its finite charge-vector squeeze is proved
independently in the library. Supporting algebra also permits off-diagonal pairs
below the diagonal; the source interpretation uses positive lifetimes. No limit
theorem for infinite diagrams or general persistence measures is claimed.

The proved equality here concerns finite real reservoir matrices; the comparison with all Borel
boundary plans is proved separately for unit-mass atomic measures
(`boundaryTransportPowerValue_ofIndexed_unit`, see
[finite weighted boundary transport](finite-weighted-boundary-transport.md)). Essential or infinite bars, arbitrary weighted inputs, completeness and
barycenters remain outside it. Quotient and metric-space instances are not supplied.
Existing first-order distance laws remain in
[the first-order matching module](finite-first-order-matching.md). The raw augmented
cost is not an ordinary metric obtained by merely collapsing the diagonal.
