# Absorption of the Reeb quotient and the geometric smoothing semigroup

## Setting

This digest continues `reeb-quotient-thickening-addition.md` and uses its objects without
redefinition. On the real slice `Over (TopCat.of ℝ)`, `T_ε = functor ε` is the product thickening,
`ℛ = ReebQuotient.quotientFunctor ℝ` is the Reeb functor and `q_X = (projNatTrans ℝ).app X` is the
Reeb projection `X ⟶ ℛ X`. On graph objects, `U_ε = geometricSmoothing ε = ℛ T_ε`
(`reeb-rgraph-smoothing.md`), and the merged `geometricSmoothingAddIso ε δ` identifies
`ℛ T_ε T_δ A` with `U_(ε+δ) A`. Write `Φ = intervalComponentsOver` for interval components and
`κ_X = intervalComponentComparison (overBaseMap X) : Φ X ⟶ Φ (ℛ X)` for the comparison of
`reeb-constructible-comparison.md`. The outer parameter comes first: `U_ε U_δ` is
`geometricSmoothing δ ⋙ geometricSmoothing ε`. Everything is in universe `0`.

## The absorption morphism and its domain

Composing two geometric smoothings needs the **absorption morphism**

```lean
ℛ (T_ε q_X) : ℛ T_ε X ⟶ ℛ T_ε ℛ X,     [(x, t)] ↦ [([x], t)]
```

to be an isomorphism at `X = T_δ A` for a graph object `A`. That object is a constructible ℝ-space
but need not be a graph object (at `δ = 0`, `zeroIso` identifies it with `A`), and its Reeb
projection `q_X` need not be an isomorphism: on the single edge, `T_(1/4)` contains two distinct points at height `1/2` joined by a constant-height path (fixture
below). So the merged `projNatIso`, which inverts `q_A` on graph objects, does not apply there. On a
graph object `A` itself absorption is immediate from `projNatIso`, and that case is only a control.

## Why no point-set inverse

A direct inverse would send `[([x], t)]` to `[(x, t)]`. That this is well defined requires lifting
constant-height paths of `T_ε ℛ X`, which are paths in `ℛ X` of varying height together with a
compensating band coordinate, through `q_X`. The library has no such path lifting, and a
compact-to-Hausdorff argument would give continuity only once bijectivity is known. The proof
therefore detects the isomorphism on interval components and reflects it.

## The `π₀` argument

* `Φ q_X = κ_X` by definition (`intervalComponentsOver_map_projNatTrans_app`), and `κ_X` is an
  isomorphism for constructible `X` (DMP Theorem 3.17, merged). The merged first-projection
  comparison `componentComparisonNatIso ε : T_ε ⋙ Φ ≅ Φ ⋙ S_ε` is hypothesis-free, so
  `Φ (T_ε q_X)` is conjugate to `S_ε (Φ q_X)` and is an isomorphism
  (`isIso_map_functor_map_projNatTrans_app`).
* The naturality square of `κ` at `g = T_ε q_X` reads
  `Φ g ≫ κ_(T_ε ℛ X) = κ_(T_ε X) ≫ Φ (ℛ g)`. Since `ℛ X` is a graph object, `T_ε ℛ X` is
  constructible and `κ_(T_ε ℛ X)` is an isomorphism, so the left side is one. Hence `κ_(T_ε X)` is
  injective at every interval. It is surjective at every interval for every space (merged), so
  `κ_(T_ε X)` is an isomorphism (`isIso_intervalComponentComparison_thickening`), although `T_ε X`
  is not claimed constructible. Cancelling it, `Φ (ℛ g)` is an isomorphism
  (`isIso_map_quotientFunctor_map_functor_map_projNatTrans_app`).

## Reflection and the hypotheses

Under

* **(H1)** `IsConstructibleSpace X`, and
* **(H2)** `IsRGraph (ℛ (T_ε X))`,

both ends of `ℛ g` are graph objects: the source by (H2), the target because `T_ε ℛ X` is
constructible. As a morphism of `RGraphCat`, its image under the merged `cosheafFunctor` is `Φ (ℛ g)`
in the full subcategory of constructible cosheaves. The inclusion of that full subcategory and
`cosheafFunctor` are fully faithful, so both reflect isomorphisms, and `ℛ g` is an isomorphism
(`isIso_quotientFunctor_map_functor_map_projNatTrans_app`). Its inverse sends `[([x], t)]` to
`[(x, t)]` (`absorption_inv_mk`), so the underlying map is a height-preserving homeomorphism.
Continuity of the inverse comes from the reflection, not from a point-set argument.

Only full faithfulness of `cosheafFunctor` is used, not its essential surjectivity or an inverse
equivalence, so no critical-value or witness scope of `cosheafEquivalence` is inherited beyond
universe `0`. No compactness, Hausdorff or local path-connectedness hypothesis is added.

**Discharge on graph objects.** For `A : RGraphCat` and `X = T_δ A`, (H1) is the merged
`isConstructibleSpace_thickening` and (H2) is the merged `isRGraph_quotient_thickening_thickening`;
both are proved, not assumed
(`isIso_quotientFunctor_map_functor_map_projNatTrans_app_thickening`). For `X = A` itself, (H1) is
`isConstructibleSpace_of_isRGraph` and (H2) follows from `isConstructibleSpace_thickening`; there the
inverse is `ℛ T_ε` of the inverse of `projNatIso`
(`inv_quotientFunctor_map_functor_map_projNatTrans_app_of_isRGraph`).

## Absorption on all constructible ℝ-spaces

For every constructible `X` and every `ε ≥ 0`, (H2) follows from (H1).
For a closed window `[a, b]`, `exists_clampData_Icc` supplies `δ > 0` and clamp data with
`lo = a`, `hi = b` on the open window `(a − δ, b + δ)`. If two points of `X|[a, b]` have Reeb
classes joined in `ℛ X|[a, b]`, then, because `κ` is injective on open intervals, they are joined
in `X|(a − δ, b + δ)`, and the clamp retracts that path into `X|[a, b]`
(`joinedIn_Icc_of_joinedIn`, `joinedIn_Icc_of_isConstructibleSpace`). By `reebRel_height_iff`,
the level sets of `T_ε X` are precisely the closed windows `X|[t−ε, t+ε]`. Consequently,
`bijective_quotientFunctor_map_functor_map_projNatTrans_app` makes `ℛ (T_ε q_X)` a continuous
bijective map; its source is compact because the constructible pieces are compact, and its target
is Hausdorff because it is a graph object, so it is a homeomorphism over `ℝ`
(`absorptionOverIso`). No Hausdorffness of the pieces is used.
Transport along this homeomorphism gives (H2) via
`isRGraph_quotient_thickening_of_isConstructibleSpace`. This route bypasses DMP15-v1
Theorem 4.27, whose constructibility conclusion for `T_ε X` is not proved here, and it needs no
Hausdorffness assumption on `X`.

The result is packaged on the full subcategory of constructible spaces as

```lean
thickeningQuotient ε : ConstructibleSpaceCat ⥤ RGraphCat
thickeningQuotientAbsorptionIso ε : thickeningQuotient ε ≅
  quotientRGraphFunctor ⋙ geometricSmoothing ε
thickeningQuotientCompIso ε δ : thickeningQuotient δ ⋙ geometricSmoothing ε ≅
  thickeningQuotient (ε + δ)
```

The last isomorphism applies `U_ε` to `thickeningQuotientAbsorptionIso δ`, then applies
`geometricSmoothingCompIso ε δ` on `ℛ X`, and then applies the inverse of
`thickeningQuotientAbsorptionIso (ε + δ)`, with only an associator between these composites. The
absorption instance `isIso_quotientFunctor_map_functor_map_projNatTrans_app_constructible` removes
(H2) from the merged absorption theorem.

Interleavings of constructible ℝ-spaces built on `thickeningQuotient` and
`thickeningQuotientCompIso` are described in
[reeb-geometric-interleaving-equivalence.md](reeb-geometric-interleaving-equivalence.md), section
*Interleavings of constructible ℝ-spaces*.

## The semigroup

On graph objects absorption assembles into the natural isomorphism

```lean
geometricSmoothingAbsorptionIso ε δ : doubleThickeningQuotient ε δ ≅ geometricSmoothing δ ⋙ geometricSmoothing ε
```

with components `ℛ (T_ε q_(T_δ A))` and inverse `[([z], t)] ↦ [(z, t)]`. Composing its inverse with
the merged `geometricSmoothingAddIso ε δ` gives

```lean
geometricSmoothingCompIso ε δ : geometricSmoothing δ ⋙ geometricSmoothing ε ≅ geometricSmoothing (ε + δ)
```

sending `[([(x, s)], t)]` to `[(x, s + t)]`, with inverse `[w] ↦ [([σ w].1, (σ w).2)]` for the
merged section `σ = addSection`. Naturality in every graph map is part of the natural isomorphism.

Parameter equalities `ε = δ` are bridged by `geometricSmoothingEqIso`, the Reeb quotient of the
band inclusions `bandEqIso`, never by `eqToIso` or casts. With it:

* **Associativity** (`geometricSmoothingCompIso_assoc`): the two composites
  `U_ε U_δ U_γ ≅ U_(ε+(δ+γ))` agree, with `(ε + δ) + γ = ε + (δ + γ)` bridged on the left.
* **Unit laws** (`geometricSmoothingCompIso_zero_left`, `geometricSmoothingCompIso_zero_right`):
  against the merged `geometricSmoothingZeroIso : U_0 ≅ 𝟭`, which sends `[(b, s)]` to `b`.

All three are checked on representatives `[([([(x, s)], t)], u)]`, where both sides give the class
of `(x, s + t + u)`.

**Cosheaf compatibility** (`cosheafFunctor_map_geometricSmoothingCompIso_hom_app`). Under the merged
comparisons `β_ε : C(U_ε A) ≅ S_ε C(A)` of Proposition 4.32, the image of the semigroup on
underlying precosheaves is the precosheaf semigroup `smoothingCompIso ε δ`:
`C(U_ε U_δ A) ⟶ C(U_(ε+δ) A) ⟶ S_(ε+δ) C(A)` equals
`C(U_ε U_δ A) ⟶ S_ε C(U_δ A) ⟶ S_ε S_δ C(A) ⟶ S_(ε+δ) C(A)`. Both send the class of
`[([(x, s)], t)]` to the class of `x`.

## Fixtures

`TDA.Reeb.QuotientThickeningAbsorptionExamples` checks the theory on the merged fixture objects.

* **Negative control.** The Reeb projection of `T_(1/4)` of the single edge is not an isomorphism:
  `(q_(1/2), 0)` and `(q_(1/4), 1/4)` are distinct, both at height `1/2`, and joined by the
  constant-height path `r ↦ (q_(1/2 - r/4), r/4)`. Absorption holds at that object.
* **Graph-object control.** On the parallel edges with `ε = 1/4`, the inverse of absorption is
  `ℛ T_(1/4)` of the inverse of `projNatIso`, and it sends `[([q_true], 1/4)]` to `[(q_true, 1/4)]`,
  computed through that description and through `absorption_inv_mk`.
* **Boundary control.** `ℛ q_X = q_(ℛ X)` for every `X`, and on the point the left unit law sends
  `[([(*, s)], 0)]` to `[(*, s)]`.
* **One edge.** At `ε = δ = 1/4`, `[([(q, 1/4)], 1/4)] ↦ [(q, 1/2)]`, the inverse returns
  `[([(q, 1/4)], 1/4)]` (the clamp of `1/2` onto `[-1/4, 1/4]` is `1/4`), associativity gives
  `[(q, 3/4)]` on both sides, and the cosheaf square at `⊤` gives the class of `q` on both sides.
* **Two merging edges.** The height-`1/2` fibre of `U_(1/4) U_(1/4)` of the parallel edges is a
  subsingleton, transported from `U_(1/4 + 1/4)` through the height-preserving semigroup
  isomorphism, and the classes over the two edges agree there, while the height-`1/2` fibre of the
  single smoothing `U_(1/4)` is not a subsingleton. The height-`1/2` fibre of `U_(1/8) U_(1/8)` is
  not a subsingleton, by injectivity of absorption from the merged statement for
  `ℛ T_(1/8) T_(1/8)`. Together these pin the threshold `ε + δ ≥ 1/2`.
* **Naturality.** On the edge swap both composites of the square send `[([(q_true, 1/4)], -1/4)]`
  to `[(q_false, 0)]`, through the merged swap square of `geometricSmoothingAddIso`; the
  representative differs from that of the identity image. The classes themselves coincide, since
  every fibre of `U_(1/4 + 1/4)` of the parallel edges is a subsingleton. At `1/8 + 1/8`, where the
  loop survives, the square separates classes: both composites send `[([(q_true, 0)], 0)]` to the
  image of `[([(q_false, 0)], 0)]`, which differs from the identity image, as `geometricSmoothingEqIso`
  carries the two classes to the distinct height-`1/2` classes over the two edges in `U_(1/4)`.
* **One point.** `(geometricSmoothingCompIso 1 1).app pointGraph` is an explicit isomorphism
  `U_1 U_1 P ≅ U_(1+1) P` in `RGraphCat`, whereas no slice isomorphism `T_1 T_1 P ≅ T_(1+1) P`
  exists (`not_iso_one_one`).
* **Flat interval.** `interval_isConstructibleSpace`, `interval_isRGraph_quotient_thickening_quarter`,
  and `interval_isIso_absorption_quarter` show that the constant-height interval is constructible
  but not a graph-object input for the merged route; its quarter-thickening has a graph quotient
  with an isomorphic absorption map.
* **Thickened pinch.** `pinch_isRGraph_quotient_thickening_quarter` and
  `pinch_thickeningQuotientAbsorptionIso_hom` show that the quarter-thickened pinch has a graph
  quotient and an isomorphic absorption component despite the non-injective attaching map.
* **Point at ε = 0 and ε = 1.** `point_isRGraph_quotient_thickening_zero`,
  `point_isRGraph_quotient_thickening_one`, and
  `point_thickeningQuotient_one_fiber_subsingleton` show that the one-point graph satisfies (H2)
  at `ε = 0` and `ε = 1`, and every fibre of its unit thickening quotient is a subsingleton.
* **Negative control.** `id_thickening_quotient_not_isRGraph` shows that the quotient of the unit
  thickening of `id ℝ` is not a graph object: the height of the unbounded input is surjective onto
  `ℝ`, while graph-object heights lie in `[T.value 0, T.value (Fin.last m)]`, so the
  constructibility hypothesis cannot be dropped.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4 **Definition 4.30** is `U_ε = ℛ T_ε`,
merged as `geometricSmoothing`. The first bullet of **Observation 4.33** asserts semigroup
isomorphisms `U_(ε₁+ε₂) ≃ U_(ε₁) U_(ε₂)`. Only its statement shape is attributed, on `RGraphCat` in
the order `U_ε U_δ ≅ U_(ε+δ)`, and it is **proved here independently** through absorption and the
merged `geometricSmoothingAddIso`. Theorem 3.17 is used as the merged
`isIso_intervalComponentComparison_of_constructible`, and Theorem 3.22 only through the full
faithfulness `cosheafFullyFaithful`.

The absorption theorem, its hypotheses (H1) and (H2), the reflection proof, the coherence laws and
the cosheaf compatibility square are library statements; none is attributed to the source.

The all-constructible absorption results and the `thickeningQuotient` packaging are library
statements, not attributions to the source.

The geometric interleavings of Definition 4.36, their distance and the inequality
`d_cosheaf ≤ d_geo` are in [reeb-geometric-interleaving.md](reeb-geometric-interleaving.md).

Not claimed here: the reverse inequality `d_geo ≤ d_cosheaf`; absorption on arbitrary objects
of the real slice; constructibility of `T_ε T_δ A`, or of `T_ε X` for a constructible `X` that
is not a graph object; a lift of `smoothingCompIso` to constructible cosheaves, so the
compatibility square is stated on underlying precosheaves.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4, Definition 4.30 and
Observation 4.33](https://arxiv.org/html/1501.04147v1).
