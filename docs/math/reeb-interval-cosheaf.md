# Interval cosheaves and smoothing

## Interval cosheaf condition

A `Type`-valued precosheaf on the interval category is a functor `F : OpenInterval ⥤ Type wF`.
An interval cover is a family `I : κ → OpenInterval` with `⋃ k, I k = J` for an interval `J`;
each member then lies in `J` (`le_of_iUnion_eq`). The predicate

```lean
IsIntervalCosheaf.{w} F :=
  ∀ ⦃κ : Type w⦄ (I : κ → OpenInterval) (J : OpenInterval) (hJ : ⋃ k, (I k : Set ℝ) = J),
    Nonempty (IsColimit (F.mapCocone (coverCocone I (le_of_iUnion_eq hJ))))
```

asks that `F` send the pairwise-intersection cocone of every interval cover to a colimit.
Overlaps are the meets `I k ⊓ I l` of the interval category, which are intersections. The cover
index universe is the first universe parameter, as for `IsPairwiseCosheaf.{w}` in `cosheaf.md`.
By the elementary correspondence of `cosheaf.md`, the condition says that every value over `J`
comes from a member and that two local values with the same image over `J` are related through
values over actual overlaps.

Covers of `⊥`, of rays and of `ℝ` are included, and so are `⊥` members; these follow the
library's convention that the interval category contains every open order-convex subset of `ℝ`.
The empty cover of `⊥` forces the empty value: an interval cosheaf has `F ⊥` empty
(`IsIntervalCosheaf.isEmpty_obj_bot`). The raw universal property, for a test object in any
`Sort`, is `IsIntervalCosheaf.existsUnique_glue`, and the condition is invariant under natural
isomorphism (`IsIntervalCosheaf.of_iso`).

The generic thin-category facts used for the value maps, `map_apply_eq_of_thin` and
`map_map_apply_of_thin`, live in `TDA.Topology.Cosheaf`: a `Type`-valued functor out of a preorder
sends parallel morphisms, and composites with the same ends, to the same map pointwise.

## Restriction from all opens

Let `G : Opens ℝ ⥤ Type u` satisfy the all-opens cosheaf condition `IsPairwiseCosheaf.{w} G`.
Its restriction `toOpensFunctor ⋙ G` along the inclusion of the interval category is an interval
cosheaf (`isIntervalCosheaf_of_isPairwiseCosheaf`). The inclusion preserves intersections, so the
overlap relation of the interval cover is that of the image cover of opens, and the union equation
`⋃ k, I k = J` gives `⨆ k, toOpens (I k) = toOpens J`. The apex change from `⨆ k, toOpens (I k)`
to `toOpens J` is then handled pointwise by the thin-category facts.

Applied to the path-component functor of a continuous `f : C(X, ℝ)` (`reeb-components-gluing.md`),
this shows that the interval component functor `intervalComponents f` of `reeb-perturbation.md` is
an interval cosheaf (`intervalComponents_isIntervalCosheaf`).

## Thickening covers and intersections

Write `T_ε I` for the thickening of `reeb-intervals.md`, with `ε : ℝ≥0`. A cover of `J` thickens
to a cover of `T_ε J`: `⋃ k, T_ε (I k) = T_ε J` (`iUnion_thicken_eq`), with no further hypothesis.

Thickening preserves the intersection of two intervals that meet:
`T_ε (I ⊓ I') = T_ε I ⊓ T_ε I'` when `I ⊓ I'` is nonempty (`thicken_inf`). It does not preserve
intersections in general. The intervals `(0, 1)` and `(2, 3)` are disjoint, so the thickening of
their intersection is `⊥`, while their `1`-thickenings meet at `3/2`.

## Interval-chain lemma

For members `I i` and `I j` of a cover of an interval `J`, let `W = T_ε (I i) ⊓ T_ε (I j)`. There
is a finite chain `i = k₀, …, kₙ = j` with

```lean
W ≤ T_ε (I kᵣ ⊓ I kᵣ₊₁)   for every r < n
```

(`reflTransGen_thicken_inf`, where the chain is a `Relation.ReflTransGen` path).

- **Empty-overlap convention.** For empty `W` the chain is the single step from `i` to `j`, since
  `W = ⊥` lies below every interval.
- **Nonempty overlap.** For nonempty `W`, consecutive original members also intersect, because
  `T_ε ⊥ = ⊥` (`reflTransGen_thicken_inf_of_nonempty`). This is the chain in the form "consecutive
  intervals meet and each thickened overlap contains `W`".
- **Containment is the content.** A chain whose consecutive members merely intersect is not
  enough. The intervals `(0, 1)` and `(-5, 1/10)` meet, but the `1`-thickening of their overlap
  misses `3/2`, which lies in `W` for `I i = (0, 1)` and `I j = (2, 3)`.

The proof uses the convex hull `S` of `I i ∪ I j`, which lies in `J` because `J` is
order-connected. Every point of `S` lies in a member whose thickening contains `W`: the members
`I i` and `I j` themselves, or, for a point between them, any member through it, since such a
point lies within `ε` of every point of `W`. Two members of this kind that meet form a chain step,
by `thicken_inf`. The members of this kind reachable from `i`, and those not reachable, give two
disjoint open sets covering `S`. As `S` is preconnected and meets the first, it lies in the first,
so `j` is reachable. Finiteness is that of the `ReflTransGen` path; no compactness is used.

## Smoothing preserves the cosheaf condition

For an interval cosheaf `F` and `ε : ℝ≥0`, the smoothing `S_ε F` of `reeb-smoothing.md` is again
an interval cosheaf, with no extra hypothesis (`isIntervalCosheaf_smoothing`):

```lean
isIntervalCosheaf_smoothing (hF : IsIntervalCosheaf.{w} F) (ε : ℝ≥0) :
    IsIntervalCosheaf.{w} ((smoothing ε).obj F)
```

The cover-wise form `smoothing_isColimit_coverCocone` deduces the condition for `S_ε F` on a
cover `I` of `J` from the condition for `F` on the thickened cover of `T_ε J`. The value of
`S_ε F` over `I k` is the value of `F` over `T_ε (I k)`, so every value over `J` still comes from a
member. In the kernel, an overlap step of `F` on the thickened cover has a witness `c` over
`W = T_ε (I i) ⊓ T_ε (I j)`. Along the interval chain from `i` to `j`, the images of `c` over the
thickened overlaps `T_ε (I k ⊓ I l)` are witnesses of overlap steps of `S_ε F`, so the two local
values are related for `S_ε F` (`eqvGen_overlapRel_smoothing`). Agreement is therefore always
established on actual overlap values. The empty-value condition is not used in this step, by the
empty-overlap convention above; the empty value of `S_ε F` follows from the theorem.

At `ε = 0` the statement is an equivalence with the hypothesis
(`isIntervalCosheaf_smoothing_zero_iff`), through the isomorphism `S_0 F ≅ F`.

## Acceptance fixtures

`TDA.Reeb.IntervalCosheafExamples` covers:

- `ε = 0`;
- disjoint members whose thickenings overlap (`disjoint_thicken_overlap`), and the cover
  `(0, 1)`, `(1/2, 5/2)`, `(2, 3)` of `(0, 3)` (`threeCover`), whose end members are disjoint and
  are joined through the middle member, both for an arbitrary interval cosheaf and for the
  interval component functor of the identity of `ℝ`;
- a member that is not a chain step although it meets an end member
  (`overlap_without_containment`);
- a cover with a `⊥` member (`cover_bot_member`), the empty cover of `⊥`, and the empty value of
  a smoothed interval cosheaf;
- the unbounded interval `ℝ = (-∞, 1) ∪ (0, ∞)` (`cover_top`);
- the smoothed interval component functor of a real-valued map.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §3.2, call a pre-cosheaf on open intervals
a cosheaf when `F(U)` is the colimit of `∐ F(I_p ∩ I_q) ⇉ ∐ F(I_p)` for every open interval `U` and
every cover of `U` by open intervals. `IsIntervalCosheaf` is this condition in the
pairwise-intersection form of `cosheaf.md`; the relation between the two diagrams is described
there.

Their Proposition 4.20 states that the smoothing of a cosheaf is a cosheaf.
`isIntervalCosheaf_smoothing` is this statement for `Type`-valued cosheaves, with the same
hypothesis. The source proof compares the two colimit diagrams for the cover and for the
thickened cover; the second has extra terms where `I_p^ε ∩ I_q^ε` is nonempty but `I_p ∩ I_q` is
empty. For such a pair it takes the compact gap `K` between the two intervals, a finite chain of
cover intervals meeting `K` with consecutive members intersecting, and notes that each thickened
chain interval contains `J = I_p^ε ∩ I_q^ε`. The interval-chain lemma states this chain with the
containment `W ≤ T_ε (I kᵣ ⊓ I kᵣ₊₁)`, which is equivalent for nonempty `W` by `thicken_inf`. The
library proves it by the connectedness of the convex hull rather than by compactness of the gap.

- The predicate quantifies over covers of `⊥`, rays and `ℝ`, and admits `⊥` members. These are
  library choices following the convention of the interval category, not statements printed in
  the paper.
- Remark 4.21 notes that the argument works in any category with an initial object. The library
  states the condition and the theorem for `Type`-valued functors only.
- The theorem is specific to covers of open intervals of `ℝ` by open intervals. Nothing here is
  claimed for covers by arbitrary open subsets or for arbitrary metric spaces; such
  generalisations would need another proof.
- Constructibility of the smoothing is not addressed.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147).
