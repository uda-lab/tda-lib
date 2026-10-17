# The Reeb quotient of the thickening addition map

## Setting

This digest continues `reeb-geometric-thickening-addition.md` and uses its objects without
redefinition. For `ε : ℝ≥0`, `Band ε = [-ε, ε]`, the thickening of `(X, f)` is `X × Band ε` with
height `height f ε (x, t) = f x + t`, and `functor ε` is the thickening on the real slice
`Over (TopCat.of ℝ)`. The addition map

```lean
addMap X ε δ : C((X × Band δ) × Band ε, X × Band (ε + δ)),   ((x, s), t) ↦ (x, s + t)
```

has the outer parameter first and is not a homeomorphism; on the one-point space no slice
isomorphism `T_1 T_1 P ≅ T_(1+1) P` exists (`not_iso_one_one`). The Reeb quotient `ℛ` is that of
`reeb-quotient.md`, with its functoriality `ReebQuotient.map` and the slice functor
`ReebQuotient.quotientFunctor ℝ` of `reeb-quotient-comparison.md`. Geometric smoothing
`geometricSmoothing ε = U_ε = ℛ T_ε` on graph objects is that of `reeb-rgraph-smoothing.md`.

This digest shows that `μ` becomes an isomorphism after the Reeb quotient, for every space and
every height function, and packages the result on the real slice and on graph objects.

## The section and the fibre paths

Write `c = projIcc (-δ) δ u` for the projection of `u ∈ Band (ε + δ)` onto `[-δ, δ]`. Then
`u - c ∈ Band ε` (`sub_projIcc_mem_band`), since `|u| ≤ ε + δ`. The section

```lean
addSection X ε δ : C(X × Band (ε + δ), (X × Band δ) × Band ε),   (x, u) ↦ ((x, c), u - c)
```

is continuous because the projection onto a closed interval is. It preserves height,
`f x + c + (u - c) = f x + u` (`height_addSection`), it is natural in every continuous map
(`addSection_natural`), and `μ ∘ σ = id` (`addMap_comp_addSection`).

For `z = ((x, s), t)` put `u = s + t`. The straight segment from `(s, t)` to `(c, u - c)` keeps `x`.
It stays in `Band δ × Band ε` because both bands are convex and both endpoints lie in them, and it
keeps the sum `s + t` at every time. So `addFiberPath z` is a path from `z` to `σ (μ z)` inside one
height fibre of `T_ε T_δ X` (`height_addFiberPath`), and `z` is Reeb-equivalent to `σ (μ z)`
(`reebRel_addSection_addMap`).

## The homeomorphism

```lean
quotientAddHomeomorph f ε δ :
    ReebQuotient (height (height f δ) ε) ≃ₜ ReebQuotient (height f (ε + δ))
```

has forward map `ℛ μ = ReebQuotient.map (addMap X ε δ) _` and inverse
`ℛ σ = ReebQuotient.map (addSection X ε δ) _`. On classes, `[z] ↦ [μ z]` and `[w] ↦ [σ w]`
(`quotientAddHomeomorph_mk`, `quotientAddHomeomorph_symm_mk`). The composite `ℛ μ ∘ ℛ σ` is the
identity because `μ ∘ σ = id`, and `ℛ σ ∘ ℛ μ` is the identity because `σ (μ z)` and `z` are joined
by the fibre path. Both maps are continuous because `ℛ` is a functor on continuous
height-preserving maps. The homeomorphism preserves height (`height_quotientAddHomeomorph`).

No compactness, Hausdorff or constructibility hypothesis is used, and the carrier universe of `X`
is arbitrary. The continuity of the inverse comes from the continuous section `σ`, not from a
compact-to-Hausdorff argument.

Two consequences are stated separately: `ℛ μ` is bijective (`bijective_quotientMap_addMap`), and
`[μ z] = [μ z']` holds exactly when `z` and `z'` are Reeb-equivalent in `T_ε T_δ X`
(`mk_addMap_eq_mk_addMap_iff`). The second is the fibre comparison: the classes of `T_ε T_δ X` in
one height fibre correspond to the classes of `T_(ε+δ) X` in the same fibre.

## The real slice and coherence

On `Over (TopCat.of ℝ)`, `ℛ μ` is an isomorphism at every object
(`isIso_quotientFunctor_map_addNatTrans_app`), since its underlying map is the homeomorphism above.
Hence

```lean
reebAddIso ε δ : (functor δ ⋙ functor ε) ⋙ ℛ ≅ functor (ε + δ) ⋙ ℛ
```

with hom `whiskerRight (addNatTrans ε δ) ℛ` (`reebAddIso_hom`) and inverse components
`ReebQuotient.map (addSection A.left ε δ) _` (`reebAddIso_inv_app_left_hom`). Naturality in every
slice morphism is part of the natural isomorphism.

Parameter equalities are bridged by `bandEqIso h : functor ε ≅ functor δ` for `h : ε = δ`, whose hom
and inverse are the band inclusions in both directions, never `eqToIso` or a cast on `Band`. The lax
laws of `addNatTrans` from `reeb-geometric-thickening-addition.md` pass through `ℛ`:

- **Associativity**, `whiskerLeft (functor γ) (reebAddIso ε δ).hom ≫ (reebAddIso (ε + δ) γ).hom ≫
  whiskerRight (bandEqIso _).hom ℛ = whiskerRight (whiskerRight (addNatTrans δ γ) (functor ε)) ℛ ≫
  (reebAddIso ε (δ + γ)).hom` (`reebAddIso_assoc`). Since every other factor is an isomorphism,
  `ℛ (T_ε μ_(δ,γ))` is one (`isIso_whiskerRight_whiskerRight_addNatTrans`), and the equation holds
  as an equation of isomorphisms with `reebAddInnerIso ε δ γ` (`reebAddIso_assoc_iso`).
- **Units** against `zeroIso`, as equations of isomorphisms: `reebAddIso 0 δ` followed by
  `bandEqIso (zero_add δ)` is `ℛ` of `zeroIso` on the inner factor, and `reebAddIso δ 0` followed by
  `bandEqIso (add_zero δ)` is `ℛ T_δ` of `zeroIso` (`reebAddIso_zero_left`,
  `reebAddIso_zero_right`).
- **Zero sections.** `ℛ` of the outer zero section followed by `ℛ μ` is `ℛ` of the enlargement
  `δ ≤ ε + δ`, and `ℛ T_ε` of the inner zero section followed by `ℛ μ` is `ℛ` of the enlargement
  `ε ≤ ε + δ` (`whiskerLeft_zeroSectionNatTrans_comp_reebAddIso`,
  `whiskerRight_zeroSectionNatTrans_comp_reebAddIso`).
- **Band enlargement** in both parameters (`reebAddIso_comp_bandInclusionNatTrans`).

Each law is the `ℛ`-image of the corresponding equation of `addNatTrans`, checked on representatives
of the Reeb classes. The slice packaging is in universe `0`.

## Graph objects

For a graph object `A`, the Reeb quotient of `T_ε T_δ A` is a graph object
(`RGraph.isRGraph_quotient_thickening_thickening`). The witness is the Reeb quotient of
`T_(ε+δ) A`, a graph object because `T_(ε+δ) A` is a constructible ℝ-space, transported along
`reebAddIso ε δ`. The double thickening `T_ε T_δ A` itself is not claimed to be constructible.

`RGraph.doubleThickeningQuotient ε δ : RGraphCat ⥤ RGraphCat` is `A ↦ ℛ T_ε T_δ A`, literally
`IsRGraph.ι ⋙ functor δ ⋙ functor ε ⋙ ℛ` under the graph inclusion
(`doubleThickeningQuotient_comp_ι`, by `rfl`). The natural isomorphism

```lean
RGraph.geometricSmoothingAddIso ε δ : doubleThickeningQuotient ε δ ≅ geometricSmoothing (ε + δ)
```

has target the merged geometric smoothing and components `ℛ μ`
(`geometricSmoothingAddIso_hom_app_hom`, by `rfl`). It is the form in which a semigroup law for
geometric smoothing would consume the addition map.

## Fixtures

`TDA.Reeb.QuotientThickeningAdditionExamples`:

- **One point.** `ℛ T_1 T_1 P ≅ ℛ T_(1+1) P` holds next to the merged `T_1 T_1 P ≇ T_(1+1) P`. The
  height-`0` segment `s ↦ ((*, s), -s)` collapses to one class, proved along the segment and again
  by injectivity of the homeomorphism from the common image `[(*, 0)]`. The height-`0` fibre of
  `ℛ T_1 T_1 P` is a subsingleton, transported from that of `T_(1+1) P`.
- **Boundary control.** At `ε = 0` on the point, the left unit law sends `[(*, s), 0]` to
  `[(*, s)]`, and the section keeps `u` in the inner band and `0` in the outer band.
- **One edge.** At `ε = δ = 1/4`, the class of `((q, 1/4), 1/4)` with `q` at height `1/2` goes to
  the class of `(q, 1/2)`, and the inverse returns it, the clamp of `1/2` being `1/4`. The
  identification `[(q, 1/4), -1/4] = [(q, 0), 0]` comes from the fibre path. Associativity at
  `[((q, 1/4), 1/4), 1/4]` gives the class with band coordinate `3/4` on both sides.
- **Two merging edges.** On the parallel edges, the classes of the points over the two edges at
  thickened height `1/2` are equal in `ℛ T_(1/4) T_(1/4)` although the points differ: their images
  lie in a subsingleton fibre of `U_(1/4 + 1/4)`. At `1/8 + 1/8` the height-`1/2` fibre of
  `ℛ T_(1/8) T_(1/8)` is not a subsingleton, transported from `U_(1/4)`. This places the threshold
  `ε + δ ≥ 1/2` of the single-parameter statement on the double thickening.
- **Naturality.** The edge-swap square of `geometricSmoothingAddIso (1/4) (1/4)` sends the class of
  the point over edge `true` to the class of the point over edge `false`.
- **Packaging.** `ℛ T_(1/4) T_(1/4)` of the parallel edges is a graph object, with its explicit
  isomorphism to `U_(1/4 + 1/4)` in `RGraphCat`.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.4 **Proposition 2.10** is the Reeb
functor, merged as `quotientFunctor`. §4.3 **Definition 4.22** is the thickening, and §4.4
**Definition 4.30** is the Reeb smoothing `U_ε = ℛ T_ε`, merged as `geometricSmoothing`. §4.4
**Observation 4.33** asserts semigroup isomorphisms `U_(ε₁+ε₂) ≃ U_(ε₁) U_(ε₂)`; this digest
prepares them but does not claim them.

The section `σ`, the fibre paths, the homeomorphism `ℛ T_ε T_δ ≅ ℛ T_(ε+δ)`, its coherence and the
graph-level isomorphism are library statements; none is attributed to the source.

Not claimed here: the absorption `ℛ T_ε ℛ ≅ ℛ T_ε`; the semigroup isomorphisms
`U_ε U_δ ≅ U_(ε+δ)` of Observation 4.33; any statement about `geometricSmoothing δ ⋙
geometricSmoothing ε`; the geometric interleavings of Definition 4.36 and any distance inequality;
constructibility of `T_ε T_δ A`.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4, Definition 4.30 and
Observation 4.33](https://arxiv.org/html/1501.04147v1).
