# The thickening addition map

## Setting

This digest continues `reeb-geometric-thickening.md` and uses its thickening without
redefinition. For `ε : ℝ≥0`, `Band ε = [-ε, ε]`, the thickening of `(X, f)` is `X × Band ε` with
height `height f ε (x, t) = f x + t`, `map g ε (x, t) = (g x, t)`, and `functor ε` is the
thickening on the real slice `Over (TopCat.of ℝ)`. The cosheaf side is the smoothing of
`reeb-smoothing.md`, with its composition isomorphism
`smoothingCompIso ε δ : smoothing δ ⋙ smoothing ε ≅ smoothing (ε + δ)`.

For product thickening, `T_ε T_δ ≅ T_(ε+δ)` is false. Over a point at height `0` with
`ε = δ = 1`, the height-`0` fibre of `T_1 T_1` is the segment `{((*, s), -s)}`, while that of
`T_2` is the single point `(*, 0)`. The correct statement is a height-preserving addition map with
lax coherence.

## The addition map

```lean
addMap X ε δ : C((X × Band δ) × Band ε, X × Band (ε + δ)),   ((x, s), t) ↦ (x, s + t)
```

The outer parameter comes first: the source is `T_ε (T_δ X)`, matching `smoothingCompIso ε δ` and
`smoothing δ ⋙ smoothing ε`. The band coordinate lies in `Band (ε + δ)` because `|s| ≤ δ` and
`|t| ≤ ε` (`add_mem_band`). The parameter `ε + δ` is never rewritten to `δ + ε`. Equalities of
parameters are bridged by `bandInclusion`, never by casts on `Band`.

The laws, each an equation of continuous maps proved on coordinates:

- **Height.** `height f (ε + δ) (addMap X ε δ z) = height (height f δ) ε z`, that is
  `f x + (s + t) = (f x + s) + t` (`height_addMap`).
- **Naturality** in every continuous `g`, with no height hypothesis (`addMap_natural`).
- **Band enlargement** in both parameters, `ε ≤ ε'` and `δ ≤ δ'` (`addMap_comp_bandInclusion`).
- **Associativity** on `((X × Band γ) × Band δ) × Band ε`, the two composites agree after
  `(ε + δ) + γ ≤ ε + (δ + γ)` (`addMap_assoc`).
- **Units.** After `0 + δ ≤ δ`, `μ_(0,δ)` is `zeroHomeomorph`; after `δ + 0 ≤ δ`, `μ_(δ,0)` is
  `T_δ` of `zeroHomeomorph` (`addMap_zero_left`, `addMap_zero_right`).
- **Zero sections.** `μ_(ε,δ)` after the outer zero section is the enlargement `δ ≤ ε + δ`, and
  after `T_ε` of the inner zero section it is the enlargement `ε ≤ ε + δ`
  (`addMap_comp_zeroSection`, `addMap_comp_map_zeroSection`).

The addition map is surjective: `(x, u)` is the image of `((x, s), u - s)` with `s` the projection
of `u` onto `[-δ, δ]`, and `|u| ≤ ε + δ` puts `u - s` in `[-ε, ε]` (`addMap_surjective`). For
nonempty `X` and `ε, δ > 0` it is not injective: with `m = min ε δ > 0`, the points `((x, 0), 0)`
and `((x, m), -m)` differ and have the same image (`addMap_not_injective`).

## The real slice

```lean
bandInclusionNatTrans (h : ε ≤ δ) : functor ε ⟶ functor δ
addNatTrans ε δ : functor δ ⋙ functor ε ⟶ functor (ε + δ)
```

The components are `bandInclusion` and `addMap` of the underlying space, by `rfl`
(`bandInclusionNatTrans_app_left_hom`, `addNatTrans_app_left_hom`). The laws above hold as
equations of natural transformations, with the associator and unitors definitional:

- associativity, `whiskerLeft (functor γ) (addNatTrans ε δ) ≫ addNatTrans (ε + δ) γ ≫
  bandInclusionNatTrans _ = whiskerRight (addNatTrans δ γ) (functor ε) ≫ addNatTrans ε (δ + γ)`
  (`addNatTrans_assoc`);
- units against `zeroIso`, `addNatTrans 0 δ ≫ bandInclusionNatTrans _ =
  whiskerLeft (functor δ) zeroIso.hom` and `addNatTrans δ 0 ≫ bandInclusionNatTrans _ =
  whiskerRight zeroIso.hom (functor δ)` (`addNatTrans_zero_left`, `addNatTrans_zero_right`);
- zero sections, `whiskerLeft (functor δ) (zeroSectionNatTrans ε) ≫ addNatTrans ε δ` and
  `whiskerRight (zeroSectionNatTrans δ) (functor ε) ≫ addNatTrans ε δ` are the enlargements
  `δ ≤ ε + δ` and `ε ≤ ε + δ`;
- band enlargement in both parameters (`addNatTrans_comp_bandInclusionNatTrans`).

So `(functor, zeroSectionNatTrans, addNatTrans)` is a lax composition law over the additive
monoid `ℝ≥0`, with unit and associativity holding up to band enlargement.

## Path components

With `ρ_ε = componentComparison f ε : C(T_ε f) ⟶ S_ε C(f)`,

```lean
intervalComponentNatTrans (addMap X ε δ) _ ≫ componentComparison f (ε + δ) =
  componentComparison (height f δ) ε ≫ (smoothing ε).map (componentComparison f δ) ≫
    (smoothingCompIso ε δ).hom.app (intervalComponents f)
```

(`addMap_comp_componentComparison`). On a representative `((x, s), t)` both sides give the class of
`x` in `f ⁻¹ (thicken (ε + δ) I)`: the left side through `(x, s + t)`, the right side through
`(x, s)`, then `x` in `f ⁻¹ (thicken δ (thicken ε I))`, then the transport of
`thickenCompIso ε δ`, which is the identity on points. The equation uses the actual
`smoothingCompIso`. On the slice it holds objectwise
(`map_addNatTrans_comp_componentComparisonNatIso`) and as an equation of natural transformations
`(functor δ ⋙ functor ε) ⋙ 𝒞 ⟶ 𝒞 ⋙ smoothing (ε + δ)`
(`whiskerRight_addNatTrans_comp_componentComparisonNatIso`).

Since every other factor is an isomorphism, `π₀` of the addition map is an isomorphism
(`isIso_intervalComponentNatTrans_addMap`, `isIso_map_addNatTrans_app`), bijective at every
interval (`intervalComponentNatTrans_addMap_app_bijective`), although the addition map is not a
homeomorphism.

## The one-point counterexample

`onePoint` is `PUnit` over height `0`. The map `fiberSegment : s ↦ ((*, s), -s)` from `Band 1` to
`T_1 T_1` of the point is injective and lands at height `0` (`fiber_zero_injective`). Every
height-`0` fibre of `T_ε` of the point is a subsingleton, since `0 + t = 0` forces `t = 0`
(`fiber_zero_subsingleton`). A slice isomorphism is injective and preserves height, so it would
send `fiberSegment 0` and `fiberSegment 1` to one point. Hence

```lean
not_iso_one_one : IsEmpty ((functor 1).obj ((functor 1).obj onePoint) ≅ (functor (1 + 1)).obj onePoint)
```

and `(addNatTrans 1 1).app onePoint` is not an isomorphism (`not_isIso_addNatTrans_app_one_one`).
The proof compares fibres; non-injectivity of `μ` alone would not exclude other isomorphisms.

## Fixtures

`TDA.Reeb.GeometricThickeningAdditionExamples`:

- **One point.** The non-isomorphism, the explicit pair `((*, 0), 0) ≠ ((*, 1), -1)` with one image
  under `μ_(1,1)`, the boundary point `(*, 2)` as the image of `((*, 1), 1)`, and bijective `π₀`
  of `μ_(1,1)` at `ℝ` on the same object.
- **Boundary control.** On the point, `μ_(0,δ)` and `μ_(ε,0)` are injective by the unit laws, so
  non-injectivity needs both parameters positive.
- **One edge.** On the realization of `singleEdge` over `0 < 1`, both sides of `height_addMap` at
  `((q, 1/4), 1/4)` with `q` at height `1/2` are `1`, and associativity at `ε = δ = γ = 1/4` gives
  band coordinate `3/4`.
- **Two merging edges.** On `parallelData`, the naturality squares of `addMap` and `addNatTrans`
  for the edge swap send the point over edge `true` at thickened height `1/2` to the point over edge
  `false`, which differs from it. The collapse onto the single edge is checked the same way; its
  one-class target alone could not detect a wrong map.
- **Distinct classes.** On the two disjoint segments, `π₀` of `μ_(1,1)` at `ℝ` sends the classes
  over the labels `false` and `true` to classes separated by `twoSegLabel` of the first coordinate.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.3 **Definition 4.22**, supplies the
thickening `X_ε = X × [-ε, ε]`, `f_ε(x, t) = f(x) + t` and `T_ε[α]` used here. Its **Proposition
4.16**, the cosheaf-side composition law, is the merged `smoothingCompIso`. §4.4 **Observation
4.33** asserts semigroup isomorphisms `U_(ε₁+ε₂) ≃ U_(ε₁) U_(ε₂)` for the Reeb smoothing
`U_ε = ℛ T_ε`.

The addition map, its coherence laws, the `π₀` compatibility and the one-point non-isomorphism are
library statements; none is attributed to the source.

Not claimed here: the Reeb quotient comparison `ℛ T_ε T_δ ≅ ℛ T_(ε+δ)`, which is proved in
[reeb-quotient-thickening-addition.md](reeb-quotient-thickening-addition.md); the absorption
`ℛ T_ε ℛ ≅ ℛ T_ε`; the semigroup isomorphisms of Observation 4.33 for geometric smoothing; the
geometric interleavings of Definition 4.36 and any distance inequality; a first projection or any
other non-height-preserving map packaged as a slice morphism. The one-point witness shows that the
analogue of Observation 4.33 for `T` itself fails.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.3, Definition 4.22, and §4.4,
Observation 4.33](https://arxiv.org/html/1501.04147v1).
