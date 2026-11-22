# Acyclic matchings for discrete Morse reduction

`TDA.Persistence.Morse.AcyclicMatching` states the semantic layer of discrete Morse
reduction for a preabstract simplicial complex `K` on any vertex type: matchings of faces,
their modified Hasse diagram, acyclicity in two equivalent forms, topological ranks, and the
filtered form for the sublevels of a `FilterFunction`. The source is Mischaikow–Nanda
([MN13](references.md#MN13)). Everything here is a predicate or a theorem about predicates;
no chain map, homology or executable check is involved.

## Matchings and the modified Hasse diagram

Faces are the elements of `TotalFace K`. The cover relation `σ ⋖ τ` of finite sets means
that `τ` has exactly one more vertex than `σ` and contains it;
`TDA.Simplicial.covBy_iff_subset_card` states this as `σ ⊆ τ ∧ #τ = #σ + 1`.

A matching is a relation `M σ τ`, read as "`σ` is matched with its codimension-one coface
`τ`". `IsMatching M` requires four conditions: every pair satisfies `σ ⋖ τ`; a face is the
lower cell of at most one pair; a face is the upper cell of at most one pair; and an upper
cell is never a lower cell. So every face lies in at most one pair, in either role.

The modified Hasse diagram `arrow M` has an arrow between every cover pair `σ ⋖ τ`:

- if `(σ, τ)` is not matched, the arrow goes from coface to face, `τ → σ`;
- if `(σ, τ)` is matched, the arrow is reversed, from face to coface, `σ → τ`.

All faces are vertices of the diagram, including unmatched faces and faces without any cover
pair. `IsAcyclic M` says that no face has a directed path back to itself
(`¬ Relation.TransGen (arrow M) x x`), and `IsAcyclicMatching M` is `IsMatching M ∧
IsAcyclic M`. The empty matching is acyclic (`isAcyclicMatching_empty`), because every
unmatched arrow lowers the face size.

## Topological ranks

A topological rank is a function `rank : TotalFace K → ℕ` with `rank u < rank v` for every
arrow `u → v` (`IsTopologicalRank`). Faces with no arrow between them may share a rank. A
topological rank rules out cycles (`IsTopologicalRank.isAcyclic`). Conversely, with finitely
many faces, every acyclic diagram has one: `isAcyclic_iff_exists_rank` takes for `rank v`
the number of faces with a path to `v`. That direction is a classical existence proof, and the finiteness
assumption is needed, since a backward-infinite path admits no ℕ-valued rank.

For a matched pair `(a_j, b_j)` and another matched lower cell `a_i` that is a facet of
`b_j`, the pair `(a_i, b_j)` is unmatched, so the diagram has the path
`a_j → b_j → a_i` and every topological rank satisfies `rank a_j < rank b_j < rank a_i`.
Thus, listing the pairs by the rank of their lower cells, a nonzero boundary entry
`D[a_i, b_j]` with `i ≠ j` only occurs when `a_j` is listed before `a_i`. This is the pivot
order that the later contraction work (#1041) relies on; this module proves only the rank
statements, not that matrix consequence.

## Comparison with MN Def. 2.2

MN work with a finite graded cell complex `(X, κ)` over a principal ideal domain, where
`ξ' ≺ ξ` means `κ(ξ, ξ') ≠ 0`. Their Def. 2.2 partitions `X` into `A`, `K` and `Q` with a
bijection `w : Q → K` such that each incidence `κ(w(Q), Q)` is a unit. The dictionary is:

| MN Def. 2.2 | Lean |
|---|---|
| `Q` (matched lower cells) | faces `σ` with `∃ τ, M σ τ` |
| `K` (matched upper cells) | faces `τ` with `∃ σ, M σ τ` |
| `A` (critical cells) | all other faces |
| `w(Q)` | the partner `τ` of `Q` |
| `ξ' ≺ ξ` | `ξ'.val ⋖ ξ.val` |

For a simplicial complex with the standard incidence, `κ(τ, σ) = ±1` exactly when `σ` is a
facet of `τ` and `0` otherwise. So `≺` becomes `⋖`, and the unit-incidence condition is the
`covBy` field of `IsMatching`; it holds over every coefficient ring, and no ring appears in
the Lean statements. The Lean predicates do not assume finitely many faces.

MN call the matching acyclic when the transitive closure of `Q' ◁ Q :⇔ Q' ≠ Q ∧ Q' ≺ w(Q)`
on `Q` is a partial order. `mnRel M Q' Q` is this generating relation, with both cells
required to be matched lower cells, and `IsMNAcyclic M` says that its reflexive-transitive
closure is antisymmetric. Because `mnRel` is irreflexive, `isMNAcyclic_iff_irrefl` shows
that this is the same as having no `mnRel` cycle.

`isAcyclic_iff_isMNAcyclic` proves, for a matching, that `IsAcyclic M ↔ IsMNAcyclic M`. The
argument is the alternating-path one:

- Every unmatched arrow lowers the face size by one and every matched arrow raises it by
  one. An upper cell is never a lower cell, so a matched arrow is never followed by another
  matched arrow.
- Hence along any path the face size rises above its starting value by at most one, and only
  at a matched upper cell. A cycle must contain a matched arrow, so it passes through a
  matched lower cell `Q₀`, and all faces on the cycle have size `#Q₀` or `#Q₀ + 1`.
- The cycle therefore alternates `Q₀ → w(Q₀) → Q₁ → w(Q₁) → ⋯ → Q₀`. Each step
  `w(Qᵢ) → Qᵢ₊₁` is an unmatched arrow, so `Qᵢ₊₁ ⋖ w(Qᵢ)` and `Qᵢ₊₁ ≠ Qᵢ`; read backwards,
  the lower cells form an `mnRel` cycle.
- Conversely, `Q' ◁ Q` gives the two-arrow path `Q → w(Q) → Q'`: the second arrow is
  unmatched because `w(Q)` is the upper cell of only one pair. An `mnRel` cycle thus lifts
  to an arrow cycle in the reverse direction.

## Filtered acyclic matchings

For `f : FilterFunction K α` over a linear order `α`, `IsGradePreserving f M` says that the
two faces of every pair have the same value. `sublevelIncl f r` views a face of the sublevel
`f.sublevel r` as a face of `K`, and `restrictSublevel f r M` keeps the pairs with both faces
in that sublevel. `IsGradePreserving.mem_sublevel_iff` shows that an equal-grade pair lies
entirely inside or entirely outside every sublevel, and
`IsAcyclicMatching.restrictSublevel` shows that the restriction of an acyclic matching to any
sublevel is again an acyclic matching. The latter needs no equal grades, because the restricted
arrows are exactly the arrows between included faces.

MN Def. 4.1 asks, for a filtration `X¹ ⊂ ⋯ ⊂ Xᴷ` of a finite complex, for an acyclic
matching `(Aᵏ, wᵏ : Qᵏ → Kᵏ)` of each frame, with `Aᵏ ⊂ Aᵏ⁺¹`, `Kᵏ ⊂ Kᵏ⁺¹`, `Qᵏ ⊂ Qᵏ⁺¹`
and `wᵏ = wᵏ⁺¹|Qᵏ`. Such a family is determined by the matching `(A, w : Q → K)` of the
final frame: the three sets partition each frame and each family is nested, so
`Qᵏ = Q ∩ Xᵏ`, `Kᵏ = K ∩ Xᵏ`, and `w(Q) ∈ Xᵏ` for `Q ∈ Qᵏ`. Conversely, a final-frame
matching whose pairs never straddle a frame restricts to such a nested family. For sublevel
frames and a finite complex (MN's setting, where the top sublevel is the final frame
`Xᴷ = X`), MN's Def. 4.1 is therefore exactly `IsFilteredAcyclicMatching f M`: a matching
whose pairs never straddle a sublevel and whose restriction to every sublevel is acyclic.
This reduction is a prose argument, not a Lean theorem.

`isFilteredAcyclicMatching_iff` proves that `IsFilteredAcyclicMatching f M` is equivalent
to `IsAcyclicMatching M ∧ IsGradePreserving f M`. Equal grades are the condition
`b(Q) = b(w(Q))` that MN use in the proof of their Thm. 4.3. In the forward direction, the
sublevel at `f σ` contains `σ` and hence its partner `τ`, so `f τ ≤ f σ`, while monotonicity
of `f` gives `f σ ≤ f τ`. With equal grades no arrow raises the grade, so a cycle through `x`
stays in the sublevel at `f x` and would be a cycle of the restricted matching. The backward
direction combines the two sublevel results above.

## What is not provided

- No executable checker or list encoding of matchings; that is a separate unit of #1039.
- No chain contraction, Morse complex or persistence invariance (#1041; a single
  cancellation is #1065), so MN Thm. 4.3 is only background here.
- No generation or search of matchings, and no maximality or optimality (#1045).
- No general cell complexes `(X, κ)` with arbitrary incidence functions, and no Lean
  statement of MN's nested family form of Def. 4.1.
