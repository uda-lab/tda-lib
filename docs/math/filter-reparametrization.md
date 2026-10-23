# Filter and diagram reparametrization, positive scaling and sup-norm Čech diagrams

This note extends [attained-grade diagram transport](sublevel-diagram-transport.md) to a
global reparametrization of filters and diagrams along order embeddings. It proves the
positive scaling law of the bottleneck distance and uses both to read the
[sup-norm value identity](cech-supnorm-witness.md) čech = rips/2 as identities of diagrams and bottleneck distances.

## Conventions

A filter function f on a complex K assigns a value in a linear order α to each face, monotonically along face inclusion. Its sublevel at r is the set of faces with value
at most r. Two filters are ordering-equivalent when they make the same weak comparisons
between face values. A diagram over α is a finite multiset of pairs (b, d) with
b ∈ α and d ∈ α ∪ {⊤} and b ≠ d. Its finite part keeps the pairs with d ≠ ⊤, and its
essential part keeps the births b of the pairs with d = ⊤. The diagram dgm_k(f, n) is the
existing diagram of sublevel homology in degree n over a field k.

Throughout, φ : α → β and ψ : β → γ are order embeddings between linear orders, that is,
maps with φ x ≤ φ y exactly when x ≤ y. An order isomorphism is a surjective order
embedding. The scaling factor c is a real number with c > 0. The factor c = 0 is
excluded, because it sends every finite pair onto the diagonal.

## Reparametrized filters

The filter f.map φ has the values φ(f(σ)). It is monotone because φ is monotone.

- **Thresholds.** For every r ∈ α, the sublevel of f.map φ at φ(r) is the sublevel of f
  at r, since φ(f(σ)) ≤ φ(r) exactly when f(σ) ≤ r. If φ is an order isomorphism e, every
  target threshold q has the form e(e⁻¹ q), so the sublevel of f.map e at q is the
  sublevel of f at e⁻¹ q. For a mere embedding, a target threshold outside the image of
  φ need not correspond to a source threshold.
- **Order.** f and f.map φ are ordering-equivalent, since φ reflects and preserves every
  weak comparison.
- **Functoriality.** Mapping along the identity does nothing, and mapping along φ and then
  ψ is mapping along ψ ∘ φ. Both follow from extensionality: filters with equal values
  are equal, because the monotonicity field is a proposition.

Positive scaling is the case φ(x) = c x, an order isomorphism of ℝ with inverse
x ↦ c⁻¹ x. The scaled sublevel at r is the original sublevel at c⁻¹ r. Scaling by 1 does
nothing, and scaling by a and then by b is scaling by b a.

Monotone maps that are not injective, and order-reversing maps, are not covered. A
non-injective monotone map can send a finite bar onto the diagonal, and negating the
values of a filter breaks monotonicity: on the two-point Rips filter a vertex has value 0
and the edge has value 2, so negated values would require 0 ≤ −2.

## Reparametrized diagrams

The diagram D.map φ maps each occurrence (b, d) to (φ b, φ d), where φ ⊤ = ⊤. Births and
finite deaths are mapped and the essential top is fixed; multiplicities are retained.

- **Off-diagonality.** If φ b = φ d for a finite d, or if φ b = ⊤ = φ d, then b = d by
  injectivity of φ on α ∪ {⊤}. This contradicts off-diagonality of D.
- **Positivity.** If b < d then φ b < φ d, because an order embedding is strictly
  increasing, and φ b < ⊤ always.
- **Parts.** The finite part of D.map φ is the finite part of D mapped coordinatewise, and
  the essential part is the essential part of D mapped by φ. Both are checked occurrence
  by occurrence, on the two cases d = ⊤ and d finite.
- **Functoriality.** The identity and composition laws hold occurrence by occurrence.

**diagrams.** For every finite complex, field and degree,

dgm_k(f.map φ, n) = dgm_k(f, n).map φ.

This is the merged attained-grade transport theorem applied to g = f.map φ. An order
embedding is strictly increasing on all of α, in particular on the attained grades, and
g(σ) = φ(f(σ)) holds by definition. The source and target value types may lie in
different universes. The merged transport theorem is pointwise and needs no global map;
this note supplies one for order embeddings.

## Positive scaling of the bottleneck distance

Write c·(x, y) = (c x, c y) for a finite pair and D.scale c for the diagram map along
x ↦ c x. For c ≥ 0 and u, v ∈ ℝ, |c u − c v| = c |u − v|. Hence

- the finite pair cost max(|x − x'|, |y − y'|) of c·p and c·q is c times that of p and q;
- the diagonal cost |y − x|/2 of c·p is c times that of p;
- the essential cost |b − b'| of c b and c b' is c times that of b and b'.

In extended nonnegative reals each identity holds after the factor ofReal c, because
ofReal(c t) = ofReal c · ofReal t for c ≥ 0.

**Matching costs.** Fix finite occurrence label types and an occurrence matching M: a
partial injection between finite labels and a bijection between essential labels. Its cost
is the maximum of the matched pair costs, the diagonal costs of unmatched labels on both
sides and the essential costs. For c ≥ 0, each term of the cost of the scaled data is c
times the corresponding term for the original data, so it is at most c · cost(M). Matched
target labels contribute zero on both sides. Thus cost(M, scaled) ≤ c · cost(M).

For c > 0, apply the same bound to the scaled data with the factor c⁻¹. Since
c⁻¹ (c t) = t, this gives cost(M) ≤ c⁻¹ · cost(M, scaled). Multiplying by c and using
c · c⁻¹ = 1 gives the reverse inequality, so cost(M, scaled) = c · cost(M).

**Presentation and diagram bottlenecks.** The presentation bottleneck is the infimum of
matching costs. Multiplication by the constant ofReal c, which is neither 0 nor ⊤, commutes
with this infimum. Hence the scaled presentation bottleneck is c times the original one.
When the essential label counts differ there is no matching; both infima are empty and
both sides equal ⊤.

The bottleneck distance of D and E is the presentation bottleneck on canonical occurrence
labels. The scaled values on the original labels present the finite and essential parts of
D.scale c and E.scale c, because those parts are the original parts mapped by scaling. The
bottleneck distance may be computed from any presentation with the same value multisets,
so

bottleneck(D.scale c, E.scale c) = c · bottleneck(D, E)

for all real diagrams D, E, including reversed finite pairs and unequal essential counts,
where both sides are ⊤. For diagrams, dgm_k(f.scale c, n) = dgm_k(f, n).scale c,
and the bottleneck distance of two scaled filters' diagrams is c times the
original one.

**Translation.** The merged translation of a filter by c is the filter map along x ↦ x + c,
and the merged translation of a diagram is the diagram map along the same isomorphism;
both identities hold value by value and occurrence by occurrence.

## Sup-norm Čech diagrams

Fix a finite ordered label type V, a finite index type ι, possibly empty, labels
p : V → (ι → ℝ) in the sup-metric product, not in `EuclideanSpace`, and a label metric d
with d(v, w) = dist(p v, p w). The merged value identity čech(s) = rips(s)/2 = 2⁻¹ rips(s)
holds for every face. Hence:

- **Filters.** The Čech filter is the Rips filter scaled by 2⁻¹, and the Rips filter is the
  Čech filter scaled by 2.
- **Diagrams.** In every degree and over every field, the Čech diagram is the Rips diagram scaled by 2⁻¹: every finite coordinate is halved and essential deaths stay
  at ⊤. This is the scaling law for diagrams applied to the filter identity; no
  second transport argument is used.
- **Bottleneck halving.** For a second configuration q with a compatible label metric e,
  the bottleneck distance of the Čech diagrams of p and q is 2⁻¹ times that of the Rips
  diagrams of d and e.
- **Stability.** Rips metric stability bounds the latter by the pairwise discrepancy δ of
  d and e, so the Čech diagrams are within δ/2.

No properness assumption is used. For labels on the line ℝ, the merged line value identity
gives the same filter and diagram identities. No line form of the halving law or the δ/2
bound is exported; the moved-point fixture derives both from the line diagram identity.

## Fixtures

- **Threshold naturality.** For the Rips filter of the points 0 and 2 on the line, scaled
  by 2, the sublevels at 2 and 4 are the original sublevels at 1 and 2. The edge is absent
  at the scaled threshold 2 and present at 4, and its scaled value is 4.
- **Order reversal.** No filter on the full complex of two labels has the negated values of
  that Rips filter.
- **Round trips.** Scaling by 2 and then by 2⁻¹ returns every real filter and every real
  diagram.
- **One vertex.** Scaling the one-vertex filter at a by c gives the one-vertex filter at
  c a. The scaling law gives the distance c |a − b| between the degree-zero diagrams at c a
  and c b, in agreement with the merged sharp value |c a − c b|.
- **Translation versus scaling.** Translating the vertex at 0 by 1 gives the vertex at 1, at
  distance 1. Scaling the vertex at 0 fixes it, at distance 0. The translation bridges are
  checked on the one-vertex filter and its diagram.
- **Infinite distance.** A diagram with one essential birth and the empty diagram are at
  distance ⊤, and their scaled diagrams remain at distance ⊤.
- **Two points on the line.** The Čech diagram of 0 and 2 is the halved Rips
  diagram in every degree over every field. At the edge the halved Rips value is
  2⁻¹ · 2 = 1, the merged Čech value.
- **The sup-norm triangle.** For (0,0), (2,0) and (1,2) in the sup-norm plane, the diagram
  identity holds in every degree, in particular for H₀ and H₁. At the triangle the halved
  Rips value 2⁻¹ · 2 = 1 is the merged Čech value.
- **A sharper bound.** Moving the point 2 to 3 changes each label distance by at most 1. The
  halving law and Rips stability bound the Čech diagrams by 1/2 in every degree, below the
  merged displacement bound 1.

## Sources

The bottleneck distance is the one of [CSEH07](references.md#CSEH07) in the library form of
the existing diagram API, and the Čech and Rips definitions are the ones matched to
[CDSO13-v3](references.md#CDSO13-v3) for the merged Čech modules. Invariance of persistence
under strictly increasing reparametrization and homogeneity of the bottleneck distance under
positive scaling are proved directly in the library. Every result here
is a library extension proved from merged definitions, and no theorem of either paper is
exported.
