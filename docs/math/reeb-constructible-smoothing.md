# Constructibility under smoothing

## Setting

Levels are `S : CriticalValues n` with `a 0 < ⋯ < a n`, and `IsConstructibleAt` is the corrected
predicate of `reeb-constructible-cosheaf.md`: finite values, bijective inclusion maps for `I ≤ J`
with **`I` nonempty** meeting the same levels, and empty values on the tails `(-∞, a 0)` and
`(a n, ∞)`. For `ε : ℝ≥0`, `thicken ε I = I + [-ε, ε]` is the thickening of
`reeb-intervals.md`, with `thicken ε ⊥ = ⊥` (`thicken_bot`), and `smoothing ε` is the smoothing
endofunctor of `reeb-smoothing.md`:

```lean
((smoothing ε).obj F).obj I = F.obj (thicken ε I)
((smoothing ε).obj F).map f = F.map ((thickenFunctor ε).map f)
((smoothing ε).map α).app I = α.app (thicken ε I)
```

(`smoothing_obj_obj`, `smoothing_obj_map`, `smoothing_map_app`, all by `rfl`). The map of
`(smoothing ε).obj F` at `I ≤ J` is therefore `F` at `thicken ε I ≤ thicken ε J`.

## Shifted critical levels

`S.shiftedSet ε : Finset ℝ` is the union of the images of `a i ↦ a i - ε` and `a i ↦ a i + ε`.
Coinciding shifts are merged by the `Finset`: at `ε = 0` the two shifts of every level coincide,
and `a i + ε = a j - ε` whenever two levels are `2ε` apart.

- Membership: `x` is in the set exactly when `x = a i - ε` or `x = a i + ε` for some `i`
  (`mem_shiftedSet`).
- The set is nonempty, with least element `a 0 - ε` and greatest element `a n + ε`, by
  monotonicity of `a` and `ε ≥ 0` (`shiftedSet_nonempty`, `min'_shiftedSet`, `max'_shiftedSet`).

The shifted witness sorts this set:

```lean
S.shiftedCount ε = (S.shiftedSet ε).card - 1
S.shifted ε : CriticalValues (S.shiftedCount ε)
(S.shifted ε).value = (S.shiftedSet ε).orderEmbOfFin (S.card_shiftedSet ε)
```

As for every `CriticalValues`, the index counts internal gaps, so the witness has
`S.shiftedCount ε + 1` levels, the cardinality of the shifted set (`card_shiftedSet`). Its public
description is:

- exact range: the levels are exactly the shifted set (`range_shifted`, `mem_range_shifted_iff`),
  so each `a i - ε` and `a i + ε` is a level (`exists_shifted_value_eq_sub`,
  `exists_shifted_value_eq_add`);
- first level `a 0 - ε` (`shifted_value_zero`) and last level `a n + ε` (`shifted_value_last`);
- a length bound: at most `2 (n + 1)` levels (`shiftedCount_le`).

The witness is not claimed minimal, and its length is not a function of `n`: for `{0, 2}` the
shifted levels at `ε = 1` are `-1, 1, 3`, three rather than four, and at `ε = 0` they are `0, 2`.
Shifts of different levels may also cross: for `{0, 2}` at `ε = 3/2` the sorted levels are
`-3/2, 1/2, 3/2, 7/2`, with `a 1 - ε` below `a 0 + ε`; this example is not a fixture.

At `ε = 0`, the shifted set is the set of levels (`shiftedSet_zero`), `S.shiftedCount 0 = n`
(`shiftedCount_zero`) and the ranges agree (`range_shifted_zero`). These equalities are
propositional; `S.shifted 0` is not identified with `S`. When the original list is wanted, the
zero comparison `smoothingZeroIso` or its lift `constructibleSmoothingZeroIso` is used.

For `ε > 0`, the same witness carries the cylinder presentation of the geometric thickening of a
finite ℝ-graph (see `reeb-rgraph-thickening.md`).

## The key interval lemma

`OpenInterval.mem_thicken_iff_of_sub_add`: let `I ≤ J` with `I` nonempty, and let each of
`a - ε` and `a + ε` lie in `I` exactly when it lies in `J`. Then `a ∈ thicken ε I` exactly when
`a ∈ thicken ε J`.

The forward direction is `thicken_mono`. Conversely, suppose `a ∈ thicken ε J` but
`a ∉ thicken ε I`, so every point of `I` is more than `ε` from `a`. Pick `x ∈ I` and `y ∈ J` with
`|a - y| ≤ ε`.

- If `x < a - ε`, then `a - ε` lies between `x` and `y`, both in `J`, so `a - ε ∈ J`. By the
  hypothesis `a - ε ∈ I`, but it is within `ε` of `a`, a contradiction.
- If `x > a + ε`, the same argument applies to `a + ε`.
- Otherwise `x` itself is within `ε` of `a`.

The argument needs one point of `I`. Applied to each old level, with both shifts among the levels
of `S.shifted ε`, it gives `value_mem_thicken_iff_of_shifted`: if nonempty `I ≤ J` meet the same
shifted levels, then `thicken ε I ≤ thicken ε J` meet the same levels of `S`.

The nonemptiness of `I` is necessary. At `S = {0}` and `ε = 1`, the intervals `⊥ ≤ (-1, 1)` meet
no shifted level `±1`, while `thicken 1 (-1, 1) = (-2, 2)` contains `0` and `thicken 1 ⊥ = ⊥` does
not.

## Constructibility of the smoothing

`CriticalValues.IsConstructibleAt.smoothing`: if `F : OpenInterval ⥤ Type u` is constructible at
`S`, then `(smoothing ε).obj F` is constructible at `S.shifted ε`, for every `ε : ℝ≥0`.

- **Finiteness.** The value at `I` is `F (thicken ε I)`, finite by hypothesis.
- **Interval rule.** For `I ≤ J` with `I` nonempty meeting the same shifted levels, the map of the
  smoothing is `F` at `thicken ε I ≤ thicken ε J`. The source `thicken ε I ⊇ I` is nonempty, and
  the two thickenings meet the same levels of `S` by the key lemma, so the rule for `F` applies.
- **Tails.** The lower tail `(-∞, a 0 - ε)` of the witness thickens to `(-∞, a 0)` (`thicken_iio`),
  the lower tail of `S`, and the upper tail `(a n + ε, ∞)` thickens to `(a n, ∞)`
  (`thicken_ioi`).

The theorem is about arbitrary precosheaves of every value universe; the cosheaf condition is not
used. At `ε = 0`, constructibility at `S.shifted 0` and at `S` are equivalent by refinement
invariance in both directions (`isConstructibleAt_shifted_zero_iff`).

`IsConstructibleCosheaf.smoothing` takes a witness of constructibility of `F`, applies the theorem
above, and supplies the cosheaf condition by `isIntervalCosheaf_smoothing` of
`reeb-interval-cosheaf.md`: the smoothing of a constructible interval cosheaf is a constructible
interval cosheaf. Thickening does not preserve intersections, and no step uses such a property.

## The restricted functor

```lean
constructibleSmoothing ε : ConstructibleCosheafCat.{u} ⥤ ConstructibleCosheafCat.{u}
constructibleSmoothing ε ⋙ ι = ι ⋙ smoothing ε
((constructibleSmoothing ε).map f).hom.app I = f.hom.app (thicken ε I)
```

`constructibleSmoothing ε` is `ObjectProperty.lift` of `ι ⋙ smoothing ε`, with the full
subcategory `ConstructibleCosheafCat` of `reeb-rgraph-cosheaf-equivalence.md`. The composite with
the inclusion, the underlying object and the underlying map are those of `smoothing ε`, by `rfl`
(`constructibleSmoothing_comp_ι`, `constructibleSmoothing_obj_obj`,
`constructibleSmoothing_map_hom`, `constructibleSmoothing_map_hom_app`).

Two structure maps are lifted, with their underlying maps the actual ones, by `rfl`:

- the unit `constructibleSmoothingUnit ε : 𝟭 ⟶ constructibleSmoothing ε`, whose component at `G`
  has underlying map `(smoothingUnit ε).app G.obj` (`constructibleSmoothingUnit_app_hom`);
- the zero comparison `constructibleSmoothingZeroIso : constructibleSmoothing 0 ≅ 𝟭`, whose
  components have underlying maps `smoothingZeroIso.hom.app G.obj` and
  `smoothingZeroIso.inv.app G.obj` (`constructibleSmoothingZeroIso_hom_app_hom`,
  `constructibleSmoothingZeroIso_inv_app_hom`).

Their naturality is that of the actual transformations, and the lifted zero unit is the inverse of
the lifted zero comparison (`constructibleSmoothingUnit_zero`, from `smoothingUnit_zero`). The
remaining smoothing structure also lifts to `ConstructibleCosheafCat`:

- `constructibleSmoothingMap h` has the refl, composition and unit-compatibility laws
  `constructibleSmoothingMap_refl`, `constructibleSmoothingMap_comp` and
  `constructibleSmoothingUnit_comp_constructibleSmoothingMap`.
- `constructibleSmoothingCompIso ε δ` has two unit laws, associativity and two zero laws,
  namely `constructibleSmoothingUnit_comp_constructibleSmoothingUnit`,
  `constructibleSmoothingUnit_comp_map_constructibleSmoothingUnit`,
  `constructibleSmoothingCompIso_assoc`, `constructibleSmoothingCompIso_zero_left` and
  `constructibleSmoothingCompIso_zero_right`; the zero laws reuse
  `constructibleSmoothingZeroIso`.
- `constructibleSmoothingCommIso ε δ` lifts the commutation isomorphism.

The underlying maps and isomorphisms are the corresponding precosheaf ones by definition. On
the cosheaves of graph objects, `constructibleSmoothing ε` and its unit correspond to the
geometric smoothing `U_ε` and its unit (see `reeb-rgraph-smoothing.md`).

## Universes

`IsConstructibleAt.smoothing`, `IsConstructibleCosheaf.smoothing`, `constructibleSmoothing` and the
lifted unit and zero comparison hold at every value universe `u`. The lifted enlargement maps,
composition isomorphisms and commutation isomorphism also hold at every value universe; a fixture
instantiates them at value universe `1`. The cosheaf condition is at cover universe `0`, as in
`IsConstructibleCosheaf`.

## Fixtures

`TDA.Reeb.ConstructibleSmoothingExamples` works with the actual smoothing of actual cosheaves:

- **`ε = 0`.** The two shifts of every level coincide; the witness of `{0, 2}` has two levels, not
  four, with range `{0, 2}`; the smoothed pinch at `ε = 0` is constructible at its own levels
  `{0, 1}`.
- **Collision.** For `{0, 2}` at `ε = 1`, the shifted set is `{-1, 1, 3}`, the count is `2`, so
  there are three levels and not four, and the levels are `-1`, `1` and `3`.
- **One level, `ε > 0`.** The shifted set of a one-level list is the pair `{a - ε, a + ε}`, with
  two levels; the smoothed point cosheaf is constructible at `{-1, 1}`.
- **Between shifted levels.** `(1/4, 3/4) ≤ (-1, 1)` meet no shifted level of `{0}` at `ε = 1`.
  The old level `0` lies outside `(1/4, 3/4)` and inside its thickening `(-3/4, 7/4)`. The key
  lemma applies, and the actual smoothed inclusion of the point cosheaf is bijective.
- **Empty source.** `⊥ ≤ (-1, 1)` also meet no shifted level, but the smoothed point cosheaf is
  empty at `⊥` and nonempty at `(-1, 1)`, so its inclusion map is not bijective
  (`emptySource_hits`, `emptySource_not_bijective`).
- **Branching pinch.** The pinch over `{0, 1}`, two edges with a common lower vertex, is
  constructible at the shifted witness after smoothing, and a constructible interval cosheaf, at
  value universes `0` and `1`. Its smoothed value at `⊥` is empty. At `ε = 1` the shifted tails are
  `(-∞, -1)` and `(2, ∞)`, where the smoothed pinch is empty; on `(-∞, 0)`, which contains the
  shifted level `-1`, it is nonempty.
- **Bundled functor.** On the pinch graph object, the lifted functor has underlying object the
  smoothed pinch, and the lifted unit and zero comparison are the pinch cosheaf applied to
  `I ≤ thicken ε I` and to `thicken 0 I = I`. For the parallel-edge swap, the lifted map has
  underlying map the smoothing of the swap, and at `ε = 1/4` it is not the identity: the
  thickening of `(1/4, 3/4)` is the gap `(0, 1)`, where the swap exchanges the two edges.
- **Lifted composition.** At `ε = δ = 1/4`, the component of the lifted composition
  isomorphism on the parallel graph is its cosheaf applied to `thickenCompIso`, and its inverse
  followed by its hom is the identity.
- **Lifted enlargement.** The map from `1` to `2` on the pinch graph is not an isomorphism,
  while the equal-parameter map at `1/4` is the identity.
- **Zero and universe controls.** The left-zero composition law holds on the single
  graph, with the stated interval component, and the composition and enlargement lifts elaborate
  at value universe `1`.
- **Commutation.** At `1/4` and `1`, the lifted commutation component on the parallel graph
  is the cosheaf map induced by the interval commutation inclusion.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.2:

- **Theorem 4.18** states that `S_ε` restricts to endofunctors of **Csh** and of **Csh**ᶜ, split
  into Propositions 4.19 and 4.20. The **Csh** half is `isIntervalCosheaf_smoothing`
  (Proposition 4.20). The **Csh**ᶜ half is `IsConstructibleCosheaf.smoothing`, with
  `constructibleSmoothing ε` the restricted endofunctor.
- **Proposition 4.19** states that `S_ε` carries constructible pre-cosheaves to constructible
  pre-cosheaves. Its proof claims that `S^ε = (S - ε) ∪ (S + ε)` is a critical set for `FΩ_ε`:
  if `I ⊆ J` and `J ∖ I` misses `S^ε`, then `J^ε ∖ I^ε` misses `S`, so
  `FΩ_ε[I ⊆ J] = F[I^ε ⊆ J^ε]` is an isomorphism; and an interval inside the tails of `S^ε`
  thickens into the tails of `S`. `IsConstructibleAt.smoothing` is the proposition at exactly this
  set, deduplicated and sorted as `S.shifted ε`, for the corrected predicate.
- **The proposition is false under the literal Definition 3.9**, which allows an empty source
  interval `I`. The point cosheaf, a singleton on intervals containing `0` and empty otherwise,
  satisfies the literal definition at `{0}`: nested intervals that both contain `0` have singleton
  values, and nested intervals that both miss it, `∅` included, have empty values. Its
  `1`-smoothing satisfies the literal definition at no finite critical set. For finite `s`, take
  `p ∈ (0, 1)` outside `s` and an open interval `W` around `p` missing `s`; then `∅ ⊆ W` both miss
  `s`, but the smoothed value at `W` is the point value at `W^1 ∋ 0`, which is nonempty, while the
  smoothed value at `∅` is empty. The failing step of the proof is the implication above at
  `I = ∅`. Both halves of this counterexample are hand arguments, not machine-checked here; the
  library checks the failing step at the shifted set `{-1, 1}` (`emptySource_hits`,
  `emptySource_not_bijective`).
- With the corrected Definition 3.9 of `reeb-constructible-cosheaf.md`, which requires a nonempty
  source, the implication holds for nonempty `I` (`value_mem_thicken_iff_of_shifted`), and
  Proposition 4.19 and the **Csh**ᶜ half of Theorem 4.18 hold as stated above.
- The source's expansion `I^ε = (a - ε, b + ε)` agrees with `thicken ε` on bounded intervals and
  rays (`thicken_ioo`, `thicken_iio`, `thicken_ioi`); functoriality of `Ω_ε` forces `∅^ε = ∅`,
  which is `thicken_bot`. The tail condition is stated on the two rays, equivalent to the source's
  form by `isEmpty_lowerTail_iff` and `isEmpty_upperTail_iff`.

Not claimed here: a minimal critical set for the smoothing or an exact length of the shifted
witness; a cast-based identification of `S.shifted 0` with `S`; any statement for cover universes
other than `0`.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.2, Theorem 4.18 and
Propositions 4.19–4.20](https://arxiv.org/html/1501.04147v1).
