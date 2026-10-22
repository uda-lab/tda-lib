# Isometry for finite-constructible real modules

For finite-constructible real persistence modules over a field, the bottleneck
of their barcode diagrams equals their extended interleaving distance.
At each finite parameter ε, an ε-interleaving exists exactly when an
occurrence matching of cost at most ε exists. The distance equality follows
by taking infima; it requires no witness at either infimum.

## Objects and assumptions

Fix a field `k : Type u` and modules `M N : PModule.{u,0,u} k ℝ`.
Let `c : Fin n ↪o ℝ` and `d : Fin m ↪o ℝ` be independent finite increasing
grids. Assume M and N are [constructible](constructible-modules.md) on their
respective grids: zero before the first critical value, constant up to natural
isomorphism on each left-closed/right-open stratum, and constant on the final
unbounded tail. The tail may be nonzero. Assume finite dimensionality only at
the original critical fibers. Constructibility derives it at all other fibers,
including observations added to a common grid. Empty grids are allowed.

Write D and E for `moduleDiagram c M hfdM` and `moduleDiagram d N hfdN`.
These diagrams come from ranks of the critical structure maps. Their
finite intervals are `[b,d)`; terminal finite-chain death represents `⊤`.
Repeated finite pairs and essential births have separate occurrence labels.
An occurrence matching has a finite partial injection and a total essential
equivalence. Its cost is the maximum of matched finite endpoint distances,
essential birth distances and unmatched diagonal costs. For a positive finite
bar the diagonal cost is `(d−b)/2`.

Both distances take values in `ℝ≥0∞`. The interleaving distance is the infimum
of all finite nonnegative parameters admitting two-map interleavings.
The bottleneck is the infimum of occurrence-matching costs. An empty infimum
is `⊤`. The two module carriers share the coefficient field's universe u,
as required by the existing finite decomposition and diagram APIs.

## Returning the shifted target

An ε-interleaving gives a comparison `M → SεN`, where
`SεN(t)=N(t+ε)`. The [induced matching](real-induced-matchings.md) constructs
a matching A from D into `translateDiagram E (−ε)`, with derived
`2ε` endpoint and unmatched-length bounds. It constructs the common grid and
derives sampled defect shortness from the interleaving equations; none of
these conclusions is supplied as an extra hypothesis.

The [target occurrence inverse](constructible-shift-diagrams.md) adds ε back.
For a selected shifted finite target `[b′,d′)`, its original endpoints are
`[b′+ε,d′+ε)`. The proved inequalities

\[
b'\le b\le b'+2\varepsilon,\qquad
d'\le d\le d'+2\varepsilon
\]

therefore give `|b−(b′+ε)|≤ε` and `|d−(d′+ε)|≤ε`.
The essential birth estimate gives the same absolute bound; the essential
occurrence equivalence remains total. Untranslating the target preserves
unmatched source status and transports the unmatched target range by a
bijection. It preserves target bar length. Both unmatched lengths are at
most `2ε`, so positivity gives diagonal costs at most ε, including equality.

`RealMatchingBounds.untranslateTarget_cost_le` proves all these contributions
are bounded by ε before bounding the finite maximum. Target-only translation
can change cost; this result uses the proved induced bounds rather than a
cost-invariance assertion. `FiniteConstructible.interleavingMatching` applies
the return operation to the constructed matching.
`interleavingMatching_cost_le` proves its ε-cost bound, including ε=0.

## Infima, equality and witness equivalence

`bottleneck_le_of_interleaving` first bounds the bottleneck by every finite interleaving parameter. `bottleneck_le_distance` then uses the defining
infimum to obtain

\[
d_B(D,E)\le d_I(M,N).
\]

It does not select a parameter equal to `d_I`, assume the distance is finite,
or select an optimal matching. If no finite interleaving exists, the right
side is infinity and the infimum argument remains valid.

The [matching-to-interleaving construction](matching-interleavings.md),
transported by the finite-constructible barcode isomorphisms, gives
the existing opposite inequality. Combining the two proves
`FiniteConstructible.bottleneck_eq_distance`:

\[
d_B(D,E)=d_I(M,N).
\]

`interleaving_iff_matching` also gives the exact finite-ε witness equivalence.
Its forward direction uses the newly constructed matching; its reverse uses
interval comparison maps and the barcode realization isomorphisms.
Both directions retain duplicates and essential tails and work across
independently sized grids.

`distance_eq_top_iff_essential_card_ne` characterizes infinity by unequal
essential occurrence cardinalities. An essential-multiplicity mismatch leaves
the matching type empty and rules out every finite interleaving. Equal finite
essential cardinalities admit a finite-cost matching. Empty diagrams have
an empty matching; their zero modules have zero distance.

The scaling consequence `bottleneck_moduleDiagram_scale` is summarized in the
[positive-scaling section](real-interleavings.md#positive-scaling) of the real
interleaving note.

## Concrete controls and limits

self-interleavings are consumed across a two-point critical grid and a
five-point refinement, deriving added finiteness and preserving duplicate
finite bars and an essential tail. The identity-induced matching with
two finite and two essential copies supplies the zero-cost boundary control.
An `[0,2)` module interleaves with zero at one; its constructed matching
leaves the finite bar unmatched and attains diagonal cost one. An essential tail versus zero has empty matching and finite-interleaving sets,
and both distances are `⊤`. Empty-grid modules and ε=0 are also checked.

[Bauer–Lesnick v4](https://arxiv.org/html/1311.3681v4), §§3.1–3.3, defines the
extended distances, δ-matchings and formal Theorem 3.5. Section 6.1,
Lemma 6.3, the `rδ` correspondence and the complete proof of Theorem 6.4 give
the forward route used here. Section 8.1, Lemma 8.1 and Theorem 8.2 give the
reverse route, implemented by the existing interval/family maps.
This equality and witness equivalence are checked specializations to the
finite, zero-left, right-continuous half-open domain above. Finite sampling,
occurrence assembly and the ENNReal infimum argument are library constructions
making that specialization explicit. Source and rights metadata are in
[BL15-v4](references.md#BL15-v4).

The source leaves Lemma 8.1's details to the reader and omits Lemma 6.2's
proof. Its Lemma 8.1(ii) has an ε/δ notation mismatch; the library's exact
half-open threshold is derived from double-shift maps. The proof of
6.1(ii) also has the documented M/N inconsistency; its formal statement
controls the specialization. No missing source proof is claimed inspected.
General decorated intervals, infinite or q-tame decompositions and isometry
over arbitrary rings or unrestricted carrier universes are outside this theorem.
The general ephemeral nonattainment example is outside this constructible
domain; the proof of equality uses no attainment assumption.

The [constructibility bridge](sublevel-constructibility.md) applies this isometry to the
sublevel modules of finite filters, whose module diagrams are their filter diagrams.
