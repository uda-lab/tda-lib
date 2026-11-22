# Acyclic matchings for discrete Morse reduction

`TDA.Persistence.Morse.AcyclicMatching` states the semantic layer of discrete Morse
reduction for a preabstract simplicial complex `K` on any vertex type: matchings of faces,
their modified Hasse diagram, acyclicity in two equivalent forms, topological ranks, and the
filtered form for the sublevels of a `FilterFunction`. The source is Mischaikow–Nanda
([MN13](references.md#MN13)). That layer consists of predicates and theorems about
predicates; no chain map or homology is involved. `TDA.Persistence.Morse.FiniteInputMatching`
adds an executable checker for matchings supplied on finite integer-graded inputs, described in
[checking a supplied matching](#checking-a-supplied-matching), and
`TDA.Persistence.Morse.FiniteInputMatchingGeneration` builds such a certified matching, described
in [generating a matching greedily](#generating-a-matching-greedily).
`TDA.Persistence.Morse.MatchingSchedule` turns a certified matching on a valid input into a
pivot schedule for the boundary and the Morse complex on its critical positions, described in
the section "The pivot schedule of a certified matching" of
[unit cancellation of a filtered chain complex](discrete-morse-cancellation.md#the-pivot-schedule-of-a-certified-matching).

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
order of #1078; this module proves only the rank statements, and
`TDA.Persistence.Morse.MatchingSchedule` proves the matrix consequence for finite inputs
(`rank_lt_of_boundary_ne_zero`, `isPivotSchedule_schedule`).

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

## Checking a supplied matching

`TDA.Persistence.Morse.FiniteInputMatching` (namespace `TDA.Persistence.Morse.MatchingInput`)
checks a matching supplied on a finite input `xs : FiniteInput.Input`. Faces are list
positions `Fin xs.length`. For a valid input (`h : Valid xs`), `listEquiv xs h` identifies
positions with the faces `TotalFace (complex xs h)` of the represented complex, and the grade
`(xs.get i).2` of position `i` is the value of `gradeFilter xs h` at that face
(`gradeFilter_listFace`). The executable predicates need no validity proof; only the transfer
theorems take `h`. This module is a library derivation over the semantic layer, attributed to
no numbered result of MN13.

### Encoding and certificate

A matching is a list `pairs : Pairs xs` of ordered (lower, upper) position pairs.
`IsMatching xs pairs` asks for three conditions:

- (N) the `2·|pairs|` endpoints `endpoints pairs` are pairwise distinct;
- (C) every pair `(i, j)` is a cover, `IsCover xs i j`: the face at `i` is a subset of the
  face at `j` with exactly one vertex fewer;
- (G) the two positions of every pair have the same grade.

A reversed pair `(upper, lower)` fails (C) and is rejected, not normalised. A pair listed twice
repeats its endpoints and fails (N), so it counts as reuse.

The certificate is a function `rank : Fin xs.length → ℕ`. The list-level diagram
`arrow xs pairs u v` has the direction of the semantic `Morse.arrow`: an unmatched cover pair
points from coface to face, and a listed pair `(u, v)` from face to coface.
`IsTopologicalRank xs pairs rank` asks for `rank u < rank v` along every such arrow between
positions. `check xs pairs rank` is the Boolean conjunction of the decisions of both
predicates, and `check_eq_true_iff` states that `check xs pairs rank = true` holds exactly when
`IsMatching xs pairs ∧ IsTopologicalRank xs pairs rank` holds. The caller supplies the rank;
`check` does not search for one.

### Semantic transfer

`toRel xs h pairs` is the relation on actual faces that holds when the positions of the two
faces form a listed pair (`toRel_listFace`). `isCover_iff_covBy` and `arrow_iff` identify the
list-level cover test and arrows with `⋖` and `Morse.arrow` on the listed faces.
`isMatching_iff` shows that `IsMatching xs pairs` is equivalent to `pairs.Nodup`, the semantic
`Morse.IsMatching (toRel xs h pairs)` and `IsGradePreserving (gradeFilter xs h) (toRel xs h
pairs)`. The condition `pairs.Nodup` appears because `toRel` forgets multiplicity: the lists
`[(B, AB), (B, AB)]` and `[(B, AB)]` give the same relation, but the first is rejected by
design. `isTopologicalRank_iff` reads a position rank as the face rank
`rank ∘ (listEquiv xs h).symm`.

`exists_check_iff` proves that some rank is accepted exactly when `pairs.Nodup` holds and
`toRel xs h pairs` is an acyclic matching with equal grades.
`exists_check_iff_isFilteredAcyclicMatching` states the same with
`IsFilteredAcyclicMatching (gradeFilter xs h) (toRel xs h pairs)`, through
`isFilteredAcyclicMatching_iff`. The direction from acyclicity to an accepted rank uses
`isAcyclic_iff_exists_rank` for the finitely many faces of the complex; it is an existence
statement, not a procedure.

### Certified matchings and critical faces

`CertifiedMatching xs` bundles `pairs`, `rank` and proofs of both list-level predicates.
`certify? xs pairs rank` returns such a bundle exactly when `check xs pairs rank = true`
(`certify?_isSome_iff`), and the bundle carries the supplied pairs and rank
(`certify?_eq_some`).

For a certified matching `c`, `c.partner i` is the other end of the pair containing `i`, if any
(`partner_eq_some_iff`, `partner_partner`). `c.critical` lists the positions without a partner
in increasing order (`critical_pairwise_lt`, `critical_nodup`), and `mem_critical_iff` shows
that they are exactly the positions in no pair. `trichotomy` states that every position is
exactly one of a matched lower cell, a matched upper cell or a critical position, and
`critical_length_add` counts `c.critical.length + 2 * c.pairs.length = xs.length`.

`c.criticalReport` lists `(i, d, g)` for each critical position `i` in the same order, with
dimension `d = (xs.get i).1.card - 1` (`FiniteInput.degree`) and original grade
`g = (xs.get i).2` (`criticalReport_map_fst`, `mem_criticalReport_iff`). For a valid input,
`isFilteredAcyclicMatching`, `isTopologicalRank_semantic` and `mem_critical_iff_listFace`
restate the certificate on actual faces.

### Fixtures

`TDA.Persistence.Morse.FiniteInputMatchingExamples` evaluates its fixtures by kernel
`decide`. Fixtures that quantify over all ranks or state a semantic fact combine such
`decide` steps with the general theorems above or with a short arithmetic argument.
Vertices `{0}`, `{1}`, … are written A, B, …. The accepted fixtures cover the
empty input, the path A–B–C, the hollow and the filled triangle, the empty matching on the
filled triangle (all seven faces critical), and the square with A, B, C, D, AB, BC, CD at
grade 0, AD at grade 1 and AC, ABC, ACD at grade 2. On the square, the pairs (B, AB),
(C, BC), (D, CD) and (AC, ABC) are accepted with the rank 10, 8, 6, 4, 9, 7, 5, 1, 2, 3, 0 by
position. The critical faces are A, AD and ACD, at dimensions 0, 1, 2 and grades 0, 1, 2
(`square_report`), and the pairs form a filtered acyclic matching of the represented complex
(`square_isFilteredAcyclicMatching`).

The rejected fixtures violate exactly one of (N), (C) and (G), each proved by `decide` together
with the other two, and no rank is accepted for them: a face used in two pairs, an identical
pair listed twice, a non-subset pair (C, AB), a codimension-two pair (A, ABC), the reversed
pair (AB, B), and the unequal-grade pair (C, BC) with grades 0 and 1.

The codimension-two pair (A, ABC) on the filled triangle also admits no rank
(`codimTwo_no_rank`): the arrows ABC → AB → A → ABC form a cycle. The same happens for every
codimension-two pair whenever (N) holds. For a pair `(σ, ρ)` with `σ ⊆ ρ` and two more
vertices in `ρ`, a valid input lists a face `e` strictly between them. Under (N) neither
`(e, ρ)` nor `(σ, e)` is a listed pair, so `ρ → e → σ` are unmatched arrows and `σ → ρ` closes
the cycle. Only the fixture case is a Lean theorem; this general argument is prose.

The cyclic circle pairs (A, AB), (B, BC) and (C, AC) on the hollow triangle satisfy (N), (C)
and (G) (`cyclic_isMatching`). Their diagram has the cycle A → AB → B → BC → C → AC → A: each
listed pair points up, and each step from an edge to its other vertex is an unmatched cover
arrow. A rank would give `rank A < rank A`, so no certificate exists
(`cyclic_no_certificate`), and the semantic relation is not acyclic
(`cyclic_not_isAcyclic`).

## Generating a matching greedily

`TDA.Persistence.Morse.FiniteInputMatchingGeneration` (namespace
`TDA.Persistence.Morse.MatchingInput`) builds a certified matching `generate xs :
CertifiedMatching xs` for every finite input `xs`, with no validity hypothesis.
`candidates xs` lists the same-grade cover pairs `(i, j)` of positions, that is the pairs with
`IsCover xs i j` and equal grades (`mem_candidates_iff`), in lexicographic (lower, upper)
order and without repetition (`candidates_nodup`). The pass starts from the empty certificate
`emptyCertified xs` (`emptyCertified_pairs`) and visits the candidates in this order. At a
candidate `p` with current certificate `c`, `greedyStep` calls `certify?` on the extended list
`c.pairs ++ [p]` with the rank `candidateRank xs (c.pairs ++ [p])`. If the checker accepts,
the returned certificate becomes the new state; otherwise `c` is kept. So `p` is accepted only
if both of its faces are still unmatched, the grades are equal, and the extended list has a
topological rank. The generated pairs are therefore a sublist of the candidates, in candidate
order (`greedyStep_pairs`, `generate_pairs_sublist`).

The state of the pass is a `CertifiedMatching` at every step, so the output needs no separate
correctness proof: it carries its pairs, its rank and proofs of both list-level predicates.
`generate_check` restates this as `check xs (generate xs).pairs (generate xs).rank = true`.
For `h : Valid xs`, `generate_isFilteredAcyclicMatching` gives
`IsFilteredAcyclicMatching (gradeFilter xs h) (toRel xs h (generate xs).pairs)`, and the
critical positions and report of the previous section apply to `generate xs`.

`candidateRank xs pairs` orients every cover pair, face to coface if it is listed and coface
to face otherwise; for a list of cover pairs, such as every extension the pass tries, these are
the arrows of its diagram. It gives every position the length of a longest chain of at most
`xs.length` consecutive such arrows ending there, by relaxation on a memoized list. Soundness
does not depend on it, since `certify?` re-checks every rank it returns. It is not claimed to
find a rank whenever the extended list is acyclic, so in general a rejected candidate is not
proved to reuse a face or close a cycle. The output depends on the list order of `xs`, and
no invariance under reordering is claimed.

`TDA.Persistence.Morse.FiniteInputMatchingGenerationExamples` evaluates the pass by kernel
`decide` on the inputs of the checker fixtures, which it imports: `empty`, the path `path`,
the same path `pathStep` with BC at grade 1, the hollow triangle `circle`, the filled triangle
`filled` and the square `square`. For each input `X`, `X_generate_pairs` and
`X_generate_report` state the generated pairs and the critical report; `empty_generate`
combines both for the empty input.

| Input | Generated pairs | Critical faces (dimension, grade) |
|---|---|---|
| `empty` | none | none |
| `path` | (A, AB), (B, BC) | C (0, 0) |
| `pathStep` | (A, AB) | B (0, 0), C (0, 0), BC (1, 1) |
| `circle` | (A, AB), (B, BC) | C (0, 0), AC (1, 0) |
| `filled` | (A, AB), (B, BC), (AC, ABC) | C (0, 0) |
| `square` | (A, AB), (B, BC), (C, CD), (AC, ABC) | D (0, 0), AD (1, 1), ACD (2, 2) |

The tree and the filled triangle reduce to one critical vertex, the hollow triangle keeps
exactly one critical vertex and one critical edge, and the square keeps one critical face per
grade. The square result differs from the hand-chosen matching of the checker fixtures, which
leaves A, AD and ACD critical; the dimensions and grades agree.

On the filled triangle the candidates are, in order, (A, AB), (A, AC), (B, AB), (B, BC),
(C, BC), (C, AC), (AB, ABC), (BC, ABC) and (AC, ABC). The pass accepts (A, AB) and (B, BC).
It rejects (A, AC), (B, AB), (C, BC), (AB, ABC) and (BC, ABC) because one of their faces is
already matched; these extensions fail (N), so no rank is accepted for them. When the pass
reaches (C, AC), its state is (A, AB), (B, BC): these are the generated pairs before (C, AC)
in candidate order, because a step only appends (`filled_generate_pairs`, `greedyStep_pairs`).
The extension closes the cycle C → AC → A → AB → B → BC → C and admits no rank
(`filled_rejected_no_certificate`), so (C, AC) is rejected and (AC, ABC) is accepted last.
The candidate list and the reuse rejections of this trace are read off by hand; that the
extension at (C, AC) admits no rank is the Lean theorem.

`pathStep_barrier` shows the filtration barrier: (B, BC) is a cover pair matched on the
constant-grade path, but on `pathStep` its grades are 0 and 1, it is not a candidate, and B
and BC stay critical (`pathStep_generate_report`). On the hollow triangle, the rejection of
(C, AC) is necessary: it is a candidate, the extended list is a list-level matching
(`circle_rejected_conditions`), and no rank is accepted for the extension
(`circle_rejected_no_certificate`), which is the cyclic circle above. These fixtures concern
specific rejections only.

MN13 §5.1 builds its matching with the coreduction-based `MorseReduce`; the proof of Thm. 5.1
(§5.2) derives its acyclicity from the order of pair excision. This greedy pass is a different,
library procedure, and no result of §5 is claimed.

## What is not provided

- Generation exists only as the greedy pass above. No maximality (by inclusion or by
  cardinality), optimality or minimal number of critical faces is claimed, nor that every
  rejected candidate reuses a face or closes a cycle; MN13 §5.1 notes that constructing an
  optimal acyclic matching is NP-hard in general. No runtime bound is stated for `check` or
  `generate`.
- The checker and generator modules of this note provide no chain contraction or Morse
  complex; for a certified matching on a valid input, they are in
  `TDA.Persistence.Morse.MatchingSchedule`, together with an isomorphism of grade-sublevel
  homology persistence modules of based complexes. For such a matching,
  `TDA.Persistence.Morse.SimplicialBridge` identifies the simplicial sublevel persistence
  module of `gradeFilter` with the persistence module of the Morse complex
  (`CertifiedMatching.morseSublevelModuleIso`); MN Thm. 4.3 remains background, since no
  source comparison is recorded.
- No general cell complexes `(X, κ)` with arbitrary incidence functions, and no Lean
  statement of MN's nested family form of Def. 4.1.
