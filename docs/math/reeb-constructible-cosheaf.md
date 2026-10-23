# Constructible interval cosheaves and finite data

## Critical levels, stars and gaps

A list of critical levels is `S : CriticalValues n`: a strictly increasing `a : Fin (n + 1) → ℝ`.
Here `n` counts the internal regular gaps, so there are `n + 1` levels. The list is a witness of
constructibility, not a minimal critical set, and it is never empty; the zero cosheaf uses a
singleton list.

With `a (-1) = -∞` and `a (n + 1) = +∞`:

- the star of level `i` is `J i = (a (i-1), a (i+1))`, so `J 0` and `J n` are rays and, for
  `n = 0`, `J 0 = ℝ`;
- the gap of edge `e : Fin n` is `K e = (a e, a (e+1))`, with endpoint levels `e.castSucc` and
  `e.succ`; gaps are nonempty and contain no level;
- the exterior tails are the rays `(-∞, a 0)` and `(a n, ∞)`.

The star bounds are defined by `Fin.cases` and `Fin.lastCases`; the cut list
`Fin (n + 3) → EReal` (`-∞`, the levels, `+∞`) gives the same bounds (`lowerCut_eq_cut`,
`upperCut_eq_cut`). A star contains exactly its own level (`value_mem_J_iff`). Adjacent stars
meet in their common gap (`J_castSucc_inf_J_succ`), nonadjacent stars are disjoint
(`J_inf_J_eq_bot`), a gap lies in a star exactly when the star is incident to it (`K_le_J_iff`),
and distinct gaps are disjoint.

## Envelopes

For an interval `I`, the envelope `N I` is the open interval between the largest level lying
below all of `I` and the smallest level lying above all of `I`, with `±∞` when there is none
(`envelope`, characterized by `mem_envelope`). For nonempty `I` meeting the levels
`a p, …, a q` it is `(a (p-1), a (q+1))`; for nonempty `I` meeting no level it is the gap or tail
containing `I`. For empty `I` the same formula gives `⊥` (`envelope_eq_bot`), so no separate
case appears in the definition.

- Extensivity: `I ≤ N I` (`le_envelope`).
- Hit preservation: for nonempty `I`, `I` and `N I` meet the same levels
  (`value_mem_envelope_iff`).
- Maximality: an interval containing nonempty `I` and meeting the same levels lies in `N I`
  (`le_envelope_of_le`). The underlying step is `le_envelope_of_hits`: an interval meeting `I`
  whose levels all lie in `I` lies in `N I`.
- Monotonicity and idempotence (`envelope_mono`, `envelope_envelope`).
- Refinement: if the levels of `S` are among those of `T`, then `N_T I ≤ N_S I`
  (`envelope_le_of_refines`).

`envelopeFunctor` and its inclusion unit `envelopeUnit : 𝟭 ⟶ N` package the envelope as an
endofunctor. **The envelope does not preserve intersections** (`exists_envelope_inf_ne`): two
disjoint nonempty subintervals of one gap or tail have the same envelope, while their intersection
has envelope `⊥`. Normalizing a cover therefore does not normalize its overlap diagram, and no
proof below does so. An intersection of two intervals that are their own envelopes is again its
own envelope (`envelope_inf_of_eq`).

The pieces are the stars, gaps and tails (`Piece`). Each piece is its own envelope
(`envelope_piece`), and every point lies in a piece containing no other level (`exists_piece`).
Hence an interval that is its own envelope is the union of the pieces it contains
(`iUnion_piece_eq`). If it meets a level, it is also the union of the stars of the levels it meets
(`iUnion_J_eq_envelope`), and a gap inside it either is the whole interval or lies in an incident
star contained in it (`K_le_envelope_cases`).

## Corrected constructibility

For `F : OpenInterval ⥤ Type u`, `S.IsConstructibleAt F` asks that

1. every value `F I` is finite;
2. for `I ≤ J` with **`I` nonempty** and `∀ i, a i ∈ I ↔ a i ∈ J`, the inclusion map
   `F.map (homOfLE _) : F I → F J` is bijective;
3. the values on the two tails are empty.

The tail condition is stated on the two rays and is equivalent to emptiness on every interval
inside them (`isEmpty_lowerTail_iff`, `isEmpty_upperTail_iff`). The cosheaf condition
`IsIntervalCosheaf` of `reeb-interval-cosheaf.md` is a separate hypothesis wherever it is used.

**Why the nonempty source.** Without it, the rule applies to `⊥ ≤ K e`: both meet no level, but
`F ⊥` is empty for every interval cosheaf while `F (K e)` may be nonempty. The strip
`PUnit × [0, 2] → ℝ` at levels `{0, 2}` satisfies the corrected predicate and refutes the
uncorrected rule (`strip_corrected_not_uncorrected`). The predicate compares only nested
intervals: two different gaps both meet no level, and they may carry different values.

The predicate is invariant under refinement of the levels (`IsConstructibleAt.of_refines`) and
under natural isomorphism (`IsConstructibleAt.of_iso`). Refinement invariance is a lemma about the
predicate; distinct presentations are not identified.

## Finite data and short maps

`FiniteReebData n` has finite vertex types `V i`, finite edge types `E e` and endpoint functions
`left e : E e → V e.castSucc`, `right e : E e → V e.succ`. Finiteness is a `Finite` field with
projected instances; no enumeration is chosen. Empty types, isolated vertices, parallel edges and
noninjective endpoints are allowed, and edges are not encoded as a relation on vertices. A map of
data (`FiniteReebData.Hom`) has vertex and edge functions commuting with both endpoint functions.
A map with bijective components has an inverse map (`Hom.inv`, `Hom.comp_inv`, `Hom.inv_comp`).
The data are indexed by `n`; the levels enter through `extract`, which always takes `S`
explicitly.

`S.extract F` has `V i = F (J i)`, `E e = F (K e)`, and the inclusion maps of `F` as
endpoint functions (`extract_left`, `extract_right`). `S.ShortMaps F G` collects functions
`F (J i) → G (J i)` and `F (K e) → G (K e)` commuting with both incidence inclusions; these are
exactly maps of the extracted data (`ShortMaps.equivHom`). Restriction `S.restrict` sends a natural
transformation to its star and gap components; its two squares are naturality squares.

## Finite determination of maps

For interval cosheaves `F` and `G` constructible at the same `S`, with covers indexed in universe
`0` (`IsIntervalCosheaf.{0}`) and values in an arbitrary universe `u`:

```lean
S.natTransEquivShortMaps hF hFc hG hGc : (F ⟶ G) ≃ S.ShortMaps F G
S.natTransEquivDiagramHom hF hFc hG hGc :
    (F ⟶ G) ≃ (S.extract F hF.finite).Hom (S.extract G hG.finite)
```

The forward map is restriction. The inverse `ShortMaps.extend` is built in three steps.

1. **Gluing on envelopes.** On an interval `U` that is its own envelope, glue the short maps over
   all pieces contained in `U`, each followed by the inclusion into `G U`
   (`ShortMaps.extendNormal`). Compatibility on two pieces uses that their intersection is its own
   envelope, hence covered by pieces, together with the naturality of the short maps for every
   inclusion of pieces (`ShortMaps.onPiece_map`): identities, the two incidence inclusions of each
   gap, and inclusions out of the empty tails. The gluing is the `IsIntervalCosheaf.existsUnique_glue`, including empty overlaps.
2. **Full naturality.** For `U ≤ V`, every piece below `U` is a piece below `V`, so naturality is
   a cover-refinement statement (`IsIntervalCosheaf.glue_comp_map`). A gap at the fringe of `V`,
   which is not an overlap of two stars selected for `V`, is itself a member of the cover of `V`,
   and its compatibility with the incident star is the incidence equation. This gives
   `β : N ⋙ F ⟶ N ⋙ G` (`ShortMaps.envelopeExtension`).
3. **Transport.** Every `G I → G (N I)` is bijective: by constructibility for nonempty `I`, and
   because both values are empty for empty `I` (`bijective_map_envelopeUnit`). The extension is
   `a_F ≫ β ≫ a_G⁻¹` with `a_F = F.map ∘ η` (`transport`), whose component at `I` is
   `(G.map η_I)⁻¹ ∘ β_I ∘ F.map η_I`.

Both inverse laws are proved (`ShortMaps.restrict_extend`, `ShortMaps.extend_restrict`), so a
transformation is determined by its star and gap components (`natTrans_ext`). On an interval that
is its own envelope and meets a level, the extension is the map glued over the selected stars
(`ShortMaps.extend_app_eq_starGlue`). That family is compatible by the incidence equations on
adjacent stars, which meet in a gap, and by the empty value at `⊥` for nonadjacent stars.

**Isomorphism criterion.** A transformation between such cosheaves is an isomorphism exactly
when all its star and gap components are bijective (`isIso_iff_shortIntervals`). For the converse
direction, the component inverses form short maps whose incidence equations follow algebraically
(`ShortMaps.inv`); their extension is a two-sided inverse by injectivity of restriction.
`ShortMaps.isIso_extend` states the same for an extension.

## Fixtures

`TDA.Reeb.ConstructibleCosheafExamples` uses only interval component functors, which are interval
cosheaves by `intervalComponents_isIntervalCosheaf`:

- singleton levels `{0}`: the star `ℝ`, no gaps, the two rays as tails; the zero cosheaf
  (components of the empty space) at every list of levels, and the point cosheaf at `{0}`, whose
  endomorphisms are all isomorphisms by the criterion;
- levels `{0, 1, 2}`: stars, gaps, overlaps and the cover of `ℝ`; envelopes of the rays
  `(-∞, 1/2)`, `(3/2, ∞)`, `(-∞, -1)` and of `ℝ`; two disjoint subintervals of `(0, 1)` with
  envelope `(0, 1)` whose intersection has envelope `⊥`; gluing over three stars, over the two
  stars of `(-∞, 2)`, over a strict refinement with a nonconstant index map, and the fringe gap
  `(1, 2)` of `(-∞, 2)`;
- the strip `A × [0, 2] → ℝ` for finite discrete `A` at `{0, 2}`: components classified by the
  first coordinate, the corrected predicate, the failure of the uncorrected rule, the extracted
  endpoint maps on representatives, and bijective endpoint maps for `A` a point;
- the collapse `Bool × [0, 2] → PUnit × [0, 2]`, which merges the two regular components over
  `(0, 2)` and so is not an isomorphism;
- refinement `{0, 2} → {0, 1, 2}`: the strip stays constructible, and the envelope of `(1/4, 3/4)`
  shrinks from `(0, 2)` to `(0, 1)`;
- levels `{0, 2, 3}`: both gaps meet no level, but the strip has a nonempty value on `(0, 2)` and
  an empty value on `(2, 3)`;
- finite data with empty values, isolated vertices, parallel edges with a noninjective endpoint, a
  noninjective map and an automorphism inverted by `Hom.inv`.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §3.3:

- **Definition 3.9** asks for finite values, isomorphisms `F[I ⊆ J]` whenever `I ∩ S = J ∩ S`,
  and empty values on intervals inside `(-∞, min S)` and `(max S, ∞)`. `IsConstructibleAt` adds
  the nonemptiness of `I`, as explained above, states the tail condition on the two rays, and keeps
  the cosheaf condition separate. The source's remark that the conditions persist for any larger
  `S` is `IsConstructibleAt.of_refines`.
- **Notation 3.11** defines `V_i`, `E_i`, `ℓ_i : E_i → V_i` and `r_i : E_i → V_{i+1}` as values
  and inclusion maps on the short intervals; `extract` has the same indices and directions.
- **Proposition 3.12** states that a morphism gives short maps satisfying
  `ψ^V_i ℓ^F_i = ℓ^G_i ψ^E_i` and `ψ^V_{i+1} r^F_i = r^G_i ψ^E_i`, and that every such family
  arises from a unique morphism. `natTransEquivShortMaps` is this statement as an equivalence,
  for `Type`-valued interval cosheaves. The construction through envelopes and transport is the
  library's; the source gives no construction at this level of detail.
- **Remark 3.13**, that a common critical set is no restriction, corresponds to refinement
  invariance applied to the union of the two lists; no union operation on `CriticalValues` is
  provided.
- **Corollary 3.14** is the "if" direction of `isIso_iff_shortIntervals`; the converse is
  immediate.

Not claimed here: a minimal critical set, a realization of finite data as a space or a cylinder
presentation, constructible ℝ-spaces and their morphisms, the equivalence of categories between
constructible cosheaves and finite data, constructibility of Reeb quotients, and any statement for
cover universes other than `0` or for non-`Type`-valued cosheaves. Constructibility of the
smoothing, at the shifted levels `(S - ε) ∪ (S + ε)`, is in `reeb-constructible-smoothing.md`.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147).
