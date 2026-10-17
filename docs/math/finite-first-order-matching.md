# Finite first-order PD matching cost

Let x and y be finite occurrence presentations of birth–death pairs (b,d) with b < d.
Births may be negative; all deaths are real and finite. There are no essential bars.
Each occurrence has unit multiplicity, so repeated pair values keep separate labels.

## Candidate costs and minimum

A partial injection M pairs selected source labels with distinct target labels. Its
real total cost S_M(x,y) is the sum of

- ‖xᵢ − yⱼ‖∞ for every matched pair;
- |death − birth|/2 for every unmatched source and target occurrence.

These are the existing `OccurrenceMatching` and `totalFiniteCost` conventions. The
first-order cost uses a sum, without a power or root. Define

m₁(x,y) = min_M S_M(x,y).

The matching family is finite, and the matching that leaves every occurrence unmatched
is always feasible. Hence the real infimum in `finiteFirstOrderMatchingCost` is an
attained minimum, including empty inputs. It is nonnegative and has two useful bounds:
every candidate cost is an upper bound on m₁, and any lower bound valid for every
candidate also bounds m₁ from below. Deleting all occurrences gives the upper bound

m₁(x,y) ≤ Σᵢ |death(xᵢ) − birth(xᵢ)|/2 + Σⱼ |death(yⱼ) − birth(yⱼ)|/2.

With one input empty, this diagonal sum is the exact value. With both inputs empty,
the value is zero. The supporting cost algebra is valid for arbitrary real pairs;
its persistence-diagram interpretation uses the positive-lifetime domain stated above.

## Occurrence labels and examples

For arbitrary equivalences u : I′ ≃ I and v : J′ ≃ J of finite occurrence types,

m₁(x ∘ u, y ∘ v) = m₁(x,y).

Relabelling gives a bijection of feasible partial matchings and preserves both cost
sums, so it also preserves the attained minimum. This changes labels without
deduplicating equal coordinates.

For one source point and one target point, the only alternatives are pairing them
or deleting both:

| Source | Target | Paired cost | Deleting both | Minimum |
|---|---|---|---|---|
| (0,4) | (1,5) | 1 | 4 | 1 |
| (0,2) | (10,12) | 10 | 2 | 2 |

Two occurrences of (0,2) sent to the empty diagram cost 2. The examples also check
coincident one-point inputs and empty inputs.

## Distance laws and zero cost

For finite presentations, the cost satisfies

- m₁(x,x) = 0;
- m₁(x,y) = m₁(y,x);
- m₁(x,z) ≤ m₁(x,y) + m₁(y,z).

These three laws also hold for arbitrary real pairs. For positive lifetimes on both
inputs, the separation statement is

m₁(x,y) = 0 if and only if there is an equivalence e : I ≃ J with x(i) = y(e(i)) for every i.

Thus zero cost preserves coordinates and their multiplicities while allowing a change
of occurrence labels. Two unequal functions related by a permutation can have zero
cost. The positivity assumption prevents an unmatched point from disappearing at zero
cost: a single diagonal point (0,0) has zero cost to the empty input, although their
occurrence types admit no bijection. Two occurrences of (0,2) and one occurrence of
(0,2) have nonzero cost.

Reversing a partial injection preserves its paired sum and exchanges the two unmatched
sums. Together with attainment, this proves symmetry. For the triangle inequality,
compose partial matchings M from x to y and N from y to z. Write δ(p)=|death−birth|/2
and d(p,q)=‖p−q‖∞. Each middle occurrence has one of four roles:

| Middle occurrence | Endpoint estimate |
|---|---|
| Selected by M and paired by N | d(xᵢ,zₖ) ≤ d(xᵢ,yⱼ)+d(yⱼ,zₖ) |
| Selected by M and deleted by N | δ(xᵢ) ≤ d(xᵢ,yⱼ)+δ(yⱼ) |
| Not selected by M, paired by N | δ(zₖ) ≤ δ(yⱼ)+d(yⱼ,zₖ) |
| Unmatched by both | No endpoint; its two nonnegative diagonal charges are unused |

The first estimate is the L∞ triangle inequality; the next two use the Lipschitz
property of distance to the diagonal. Summing source paths uses N's source charges
at middle labels selected by M. Summing the remaining target paths uses the first
matching's unmatched-middle charges and N's source charges at the complementary
labels, together with N's unmatched-target charges. Partial injectivity counts each
selected contribution once. This partitions N's source sum without spending a middle
charge twice. The composed cost is at most S_M(x,y)+S_N(y,z). Apply this bound to
attained minimizers to obtain the triangle inequality for m₁.

For separation, a zero-cost minimizer has all nonnegative charges zero. Positive
lifetimes prohibit unmatched occurrences on either side, so the partial injection
is a bijection. Each zero L∞ pair cost forces equal birth–death values. Conversely,
a value-preserving equivalence has zero cost by reindexing the self-cost theorem.

## Gaussian persistence-image bound

Use the same bandwidth σ > 0, weight and pixel family on both inputs, as in the
[Gaussian PI construction](persistence-images.md). On birth–persistence coordinates,
the weight is nonnegative, bounded by B, globally A-Lipschitz in the maximum norm,
and zero at persistence zero, with A,B ≥ 0. Pixels form a fixed finite measurable
pairwise disjoint family. Write C = 2A + 3B sqrt(2/π)/σ. Then the actual pixel vectors
in `PiLp 1` satisfy

‖PI(x) − PI(y)‖₁ ≤ C m₁(x,y).

Choose an attaining matching and apply the existing every-matching Gaussian estimate.
Its cost is exactly m₁, so no limiting argument or unproved optimizer hypothesis is
needed. The Gaussian integrals and their analytic estimates remain those of the
existing PI construction.

## Interfaces and source scope

`TDA.Persistence.FiniteMatchingCost` supplies the minimum, attainment, candidate and
universal lower bounds, empty-input formulas and reindexing theorem.
`TDA.Persistence.FiniteMatchingCostLaws` supplies real total-cost reversal/composition,
the three distance laws and the positive-lifetime zero-cost characterization.
`TDA.Persistence.PersistenceImageMatching` supplies
`norm_image_sub_le_finiteFirstOrderMatchingCost`. Ordinary `TDA.Persistence` includes
these modules. These are noncomputable mathematical APIs, without a numerical optimizer.

[Figalli–Gigli](references.md#FG10) is the prior boundary-transport reference: its
Problem 1.1 uses a bounded open Euclidean domain and quadratic Euclidean cost;
Lemma 2.1 and Theorem 2.2 prove measure gluing and distance laws in that setting.
[Divol–Lacombe corrected v4](references.md#DL20-v4), formula (1), supplies the
partial-matching convention with p=1 and ground q=∞ used for this finite occurrence
model. The minimum, finite matching laws and PI corollary are proved directly in the
library. The paper's Appendix B uses measure gluing for its metric laws, whereas the
finite proof above allocates individual occurrence charges. Their
Proposition 3.2 identifies diagram matching with measure partial transport.
[Finite boundary transport](finite-boundary-transport.md) separately proves equality
with an optimization over all feasible finite real reservoir matrices, using
cost-preserving augmented assignments and mathlib's Birkhoff decomposition. Completion
is a section of restriction; the dummy assignments are not unique. Equality with all
Borel/Radon couplings remains unproved. No quotient or metric-space instance on raw
presentations is supplied.
[Finite real-exponent boundary transport](finite-p-boundary-transport.md) supplies powered
and rooted optima and their finite-plan identification for real p≥1. General-p metric
laws, essential bars, noninteger input measures and infinite diagrams remain separate.
