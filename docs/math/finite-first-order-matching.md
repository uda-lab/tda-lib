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
`TDA.Persistence.PersistenceImageMatching` supplies
`norm_image_sub_le_finiteFirstOrderMatchingCost`. Ordinary `TDA.Persistence` includes
both modules. These are noncomputable mathematical APIs, without a numerical optimizer.

[Figalli–Gigli](references.md#FG10) is the prior boundary-transport reference: its
Problem 1.1 uses a bounded open Euclidean domain and quadratic Euclidean cost.
[Divol–Lacombe corrected v4](references.md#DL20-v4), formula (1), supplies the
partial-matching convention with p=1 and ground q=∞ used for this finite occurrence
model. The minimum and PI corollary are proved directly in the library. Their
Proposition 3.2 identifies diagram matching with measure partial transport; that
identification, including the real coupling optimization, is outside this unit.

No full boundary-augmented-bijection equivalence, triangle inequality, identity of
indiscernibles modulo permutation, or metric-space instance is proved here. General p,
essential bars, noninteger measures and infinite diagrams require separate results.
