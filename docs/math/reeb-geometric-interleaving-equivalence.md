# Geometric and cosheaf interleavings of graph objects coincide

## Setting

This digest continues `reeb-geometric-interleaving.md` and uses its objects without redefinition:
`U_ε = geometricSmoothing ε`, `ζ^ε` the geometric unit, `μ_(ε,δ) : U_ε U_δ ≅ U_(ε+δ)`,
`C = cosheafFunctor : RGraphCat ⥤ ConstructibleCosheafCat`,
`β^ε : U_ε ⋙ C ≅ C ⋙ constructibleSmoothing ε`, `S_ε = smoothing ε` on interval precosheaves, and
the shifted map

```lean
cosheafShiftMap φ = (C φ).hom ≫ β^ε_B : (C A).obj ⟶ S_ε (C B).obj      (φ : A ⟶ U_ε B).
```

The outer parameter comes first, interleaving parameters are the literal `ε + ε` and `ε + δ`, and
everything is in universe `0`.

## The shifted-map bijection

`cosheafShiftEquiv ε A B : (A ⟶ U_ε B) ≃ ((C A).obj ⟶ S_ε (C B).obj)` has `cosheafShiftMap` as
its forward map, by definition. Its inverse sends `f` to the preimage under `C` of
`f ≫ (β^ε_B)⁻¹`. Three facts make this work.

* **Maps need no constructibility proof.** `ConstructibleCosheafCat` is a full subcategory, so a
  morphism of constructible cosheaves is exactly a natural transformation of the underlying
  precosheaves. The composite `f ≫ (β^ε_B)⁻¹ : (C A).obj ⟶ (C (U_ε B)).obj` is therefore a morphism
  `C A ⟶ C (U_ε B)` as it stands.
* **`C` is fully faithful** (`cosheafFullyFaithful`), on all graph objects and without
  hypotheses, so that morphism has a unique preimage `A ⟶ U_ε B`.
* **`β^ε_B` is an isomorphism**, so composing with it and with its inverse cancel.

`S_ε (C B).obj` is not definitionally `(C (U_ε B)).obj`; the two are related only through `β^ε_B`.
Consequently `cosheafShiftMap` is injective, and every natural transformation
`(C A).obj ⟶ S_ε (C B).obj` is a shifted map.

The composite law of `reeb-geometric-interleaving.md` returns to the source object. Its proof never
uses that, and it holds in the three-object form

```lean
cosheafShiftMap (φ ≫ U_ε ψ ≫ μ_(ε,δ) at D) =
  cosheafShiftMap φ ≫ S_ε (cosheafShiftMap ψ) ≫ smoothingCompIso ε δ at (C D).obj
```

for `φ : A ⟶ U_ε B` and `ψ : B ⟶ U_δ D` (`cosheafShiftMap_comp'`).

## The equivalence of interleavings

A precosheaf `ε`-interleaving `j` of `(C A).obj` and `(C B).obj` gives a geometric one,
`GeometricInterleaving.ofCosheaf j`, whose maps are the preimages of `j.φ` and `j.ψ` under the
bijection. For its first triangle, apply `cosheafShiftMap` to both sides. The composite law and
the bijection turn the left side into `j.φ ≫ S_ε j.ψ ≫ smoothingCompIso ε ε`, which is the
precosheaf unit at `ε + ε` by the triangle of `j`. The unit law turns the right side `ζ^(ε+ε)` into
the same unit. Injectivity gives the geometric triangle. The mirror triangle is the same argument.

`ofCosheaf` and `toCosheaf` are mutually inverse, so

```lean
GeometricInterleaving.cosheafEquiv ε A B :
  GeometricInterleaving ε A B ≃ Interleaving ε (C A).obj (C B).obj
```

with forward map `toCosheaf`, at every parameter `ε`. In particular a geometric `ε`-interleaving
exists exactly when a precosheaf one does.

## `d_geo = d_cosheaf`

```lean
geometricInterleavingDistance A B = interleavingDistance (C A).obj (C B).obj.
```

The inequality `≥` is the merged `d_cosheaf ≤ d_geo`. The inequality `≤` is new: every precosheaf
witness gives a geometric witness at the same parameter. The approximation-from-above form

```lean
geometricInterleavingDistance A B < r ↔ ∃ ε : ℝ≥0, ε < r ∧ Nonempty (GeometricInterleaving ε A B)
```

holds directly from the infimum. Zero distance is transported from the precosheaf law: it means
geometric witnesses at every positive parameter. It is not a statement about `0`-witnesses, and
zero distance does not give `A ≅ B`.

## Composition and the triangle inequality

Composition is defined by transport,

```lean
GeometricInterleaving.trans i j = ofCosheaf (i.toCosheaf.trans j.toCosheaf)
```

for `i` at `ε` and `j` at `δ`, landing at `ε + δ`. So its cosheaf image is the precosheaf composite
with no triangle proof. Its first component is the geometric shifted composite
`A ⟶ U_ε B ⟶ U_ε U_δ D ≅ U_(ε+δ) D`, by the three-object composite law and injectivity
(`GeometricInterleaving.trans_φ`).

A direct geometric definition would also have to produce the second component of the precosheaf
composite, which ends with the band inclusion of `δ + ε = ε + δ`. Its geometric counterpart is the
band-inclusion isomorphism `geometricSmoothingEqIso`, and the compatibility of `cosheafShiftMap`
with it is not merged. The transport route avoids it, and no formula for the second component is
claimed.

The triangle inequality for `d_geo` and invariance under isomorphism of graph objects, in both
arguments, follow from the equality and the precosheaf results. The distance stays a plain
function; no `EDist`, `PseudoEMetricSpace` or `MetricSpace` instance is installed.

## Fixtures

* **Round trip.** The geometric `1/2`-interleaving of the single edge and its midpoint is
  recovered from its precosheaf interleaving, and its first precosheaf map is the shifted map of
  its preimage.
* **Exact cosheaf distance.** The component precosheaves of the edge and its midpoint are at
  interleaving distance exactly `1/2`, sharpening the merged upper bound, and they admit no
  precosheaf `ε`-interleaving for `ε < 1/2`. The component precosheaves of the two parallel edges
  and the single edge admit no `0`-interleaving.
* **Composite witness.** The `1/4`-interleaving of the parallel edges with the edge, composed with
  the `1/2`-interleaving of the edge with its midpoint, is a geometric `(1/4 + 1/2)`-interleaving,
  with its cosheaf image and its first component written out. The triangle inequality gives
  `d_geo(parallel edges, midpoint) ≤ 1/4 + 1/2`; no exact value is claimed.
* **Presentations.** The edge over `0 < 1/2 < 1` is at distance `1/2` from the midpoint, by
  invariance under the subdivision isomorphism.
* **Zero distance.** The two presentations of the edge have witnesses at every positive parameter;
  the edge and its midpoint do not.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4. As in `reeb-geometric-interleaving.md`,
only the statement shapes of **Definition 4.36** and **Definition 4.4** are attributed. The
bijection, the equivalence of geometric and cosheaf interleavings, `d_geo = d_cosheaf`,
composition, the triangle inequality, isomorphism invariance and the zero-distance law are
**library statements proved from merged facts**: full faithfulness of `C`, invertibility of `β^ε`
and the unit and composite laws of the shifted map. None is attributed to a numbered source result.
Essential surjectivity of `C` is not used, so no critical-value scope is inherited.

Not claimed here: enlargement `U_ε ⟶ U_ε'` for `ε ≤ ε'`, `GeometricInterleaving.mono` and
`d_geo(A, U_ε A) ≤ ε`; a formula for the second component of `trans`; a lift of `smoothingCompIso`
to constructible cosheaves; absorption beyond (H2); a comparison with Mapper; interleavings of
precosheaves that do not come from graph objects.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4, Definition
4.36](https://arxiv.org/html/1501.04147v1).
