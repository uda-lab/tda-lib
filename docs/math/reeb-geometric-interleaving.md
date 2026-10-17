# Geometric interleavings of graph objects

## Setting

This digest continues `reeb-quotient-thickening-absorption.md` and uses its objects without
redefinition. On graph objects, `U_ε = geometricSmoothing ε`, `ζ^ε = geometricSmoothingUnit ε :
𝟭 ⟶ U_ε` is the geometric unit, `μ_(ε,δ) = geometricSmoothingCompIso ε δ : U_ε U_δ ≅ U_(ε+δ)` is
the semigroup isomorphism, `C = cosheafFunctor` is the component functor and
`β^ε = geometricSmoothingComparisonIso ε : U_ε ⋙ C ≅ C ⋙ constructibleSmoothing ε` is the
comparison of DMP Proposition 4.32. On precosheaves, `S_ε = smoothing ε`, `σ^ε = smoothingUnit ε`
and `smoothingCompIso` are as in `reeb-smoothing.md`. The outer parameter comes first:
`U_ε U_δ = geometricSmoothing δ ⋙ geometricSmoothing ε`. Everything is in universe `0`.

## Geometric interleavings

A **geometric `ε`-interleaving** `GeometricInterleaving ε A B` of graph objects is a pair

```lean
φ : A ⟶ U_ε B,     ψ : B ⟶ U_ε A
```

whose shifted composites are the units:

```lean
φ ≫ U_ε ψ ≫ μ_(ε,ε) = ζ^(ε+ε) at A,     ψ ≫ U_ε φ ≫ μ_(ε,ε) = ζ^(ε+ε) at B.
```

These are equations of morphisms in `RGraphCat` into the merged `U_(ε+ε)`. The parameter is the
literal `ε + ε`, exactly as in the precosheaf `Interleaving` of `reeb-smoothing.md`; it is never
rewritten to `2ε`. Interleavings have extensionality, a symmetry swapping `φ` and `ψ`, and the unit
interleaving `refl ε A` with `φ = ψ = ζ^ε`.

## Unit coherence

The unit is coherent with the semigroup in both orders:

```lean
ζ^δ ≫ ζ^ε (U_δ A) ≫ μ_(ε,δ) = ζ^(ε+δ),     ζ^ε ≫ U_ε ζ^δ ≫ μ_(ε,δ) = ζ^(ε+δ).
```

Both send `x` to `[([(x, 0)], 0)]` and then to `[(x, 0 + 0)] = [(x, 0)]`. A parameter equality
`ε = δ` fixes the unit through the band-inclusion isomorphism `geometricSmoothingEqIso`, never
through a cast. In the triangles that isomorphism is not needed, since the merged unit already sits
at `ε + ε`. It enters only at `ε = 0`, where `μ_(0,0)` targets `U_(0+0)` and the merged left unit
law relates it to `U_0 ≅ 𝟭` through `geometricSmoothingEqIso (zero_add 0)`.

## `0`-interleavings are isomorphisms

An isomorphism `e : A ≅ B` gives the `0`-interleaving `e.hom ≫ ζ^0`, `e.inv ≫ ζ^0`, by naturality
of `ζ^0` and unit coherence. Conversely a `0`-interleaving gives `A ≅ B` with
`hom = φ ≫ (U_0 ≅ 𝟭)` and `inv = ψ ≫ (U_0 ≅ 𝟭)`: naturality of `U_0 ≅ 𝟭` at `ψ`, the merged left
unit law, the triangle, unit coherence at `0 + 0 = 0` and `ζ^0 = (U_0 ≅ 𝟭)⁻¹` give the inverse
laws. So `Nonempty (GeometricInterleaving 0 A B) ↔ Nonempty (A ≅ B)`. No round-trip equivalence is
claimed.

## The distance

```lean
geometricInterleavingDistance A B = ⨅ (ε : ℝ≥0) (_ : Nonempty (GeometricInterleaving ε A B)), ε
```

in `ℝ≥0∞`. A witness bounds it, it has the lower-envelope characterization, it is `⊤` exactly when
no interleaving exists, it is `0` on `A, A` and on isomorphic objects, and it is symmetric. The
triangle inequality is **not yet proved**. The distance is a plain function: no `EDist`,
`PseudoEMetricSpace` or `MetricSpace` instance is installed.

## Transport to the cosheaf side

The **shifted map** of `φ : A ⟶ U_ε B` on underlying precosheaves is

```lean
cosheafShiftMap φ = (C φ).hom ≫ β^ε_B : C A ⟶ C (U_ε B) ≅ S_ε C B.
```

It uses exactly three merged facts.

* **Unit.** `cosheafShiftMap ζ^ε = σ^ε`, which is the merged unit compatibility (DMP
  Proposition 4.35).
* **Naturality of `β^ε`.** It moves `C (U_ε ψ)` past `β^ε`.
* **The semigroup square.** `cosheafFunctor_map_geometricSmoothingCompIso_hom_app` turns
  `C μ_(ε,δ)` followed by `β^(ε+δ)` into `β^ε`, `S_ε β^δ` and `smoothingCompIso`.

With them, `cosheafShiftMap (φ ≫ U_ε ψ ≫ μ_(ε,δ)) = cosheafShiftMap φ ≫ S_ε (cosheafShiftMap ψ) ≫
smoothingCompIso`, for arbitrary `ε`, `δ`. So a geometric `ε`-interleaving gives a precosheaf
`ε`-interleaving `toCosheaf` of `(C A).obj` and `(C B).obj`, compatible with symmetry, and

```lean
interleavingDistance (C A).obj (C B).obj ≤ geometricInterleavingDistance A B.
```

The left side is the merged distance on the actual underlying precosheaves. Neither the full
faithfulness `cosheafFullyFaithful` nor the equivalence `cosheafEquivalence` is used, so no
critical-value or witness scope is inherited.

## Thin targets

Two graph maps into a target whose height fibres are subsingletons are equal, since both send `x`
into the fibre over the height of `x`. Every fixture triangle below is closed this way.

## Fixtures

* **Unit coherence.** On the single edge over `0 < 1` at `ε = δ = 1/4`, both forms send the edge
  point `q` at height `1/2` to `[(q, 0)]` in `U_(1/4 + 1/4)`.
* **The edge against its midpoint.** `P` is one vertex at height `1/2`, and the edge spans
  `[0, 1]`. The maps `x ↦ [(p, f x - 1/2)]` and `p ↦ [(q, 0)]` form a `1/2`-interleaving. Every point
  of `U_ε P` has height in `[1/2 - ε, 1/2 + ε]`, so for `ε < 1/2` the top vertex, at height `1`,
  has no image and no `ε`-interleaving exists. Hence `d_geo(edge, P) = 1/2` exactly, in `ℝ≥0∞`, and
  the cosheaf interleaving distance is at most `1/2`. The midpoint is used so that the threshold is
  half the height span; at the endpoint vertex `0` the same argument gives `1`.
* **Two merging edges against one edge.** The collapse and the inclusion of the edge `false`,
  followed by `ζ^(1/4)`, form a `1/4`-interleaving: `U_(1/4 + 1/4)` of both graphs has subsingleton
  fibres. So `d_geo ≤ 1/4`, and the cosheaf distance too. At `1/8` the same-shaped pair fails its
  first triangle: at the edge point over `true` the composite gives `[(q_false, 0 + 0)]` and the
  unit gives `[(q_true, 0)]`, which are distinct after `U_(1/8 + 1/8) ≅ U_(1/4)`. This concerns
  that specific pair only; it is not claimed that no `1/8`-interleaving exists.
* **Negative controls.** No `0`-interleaving exists between the parallel edges and the single
  edge, which are not isomorphic, and none between the edge and its midpoint.
* **Identity and presentations.** The unit `0`-interleaving of the parallel edges returns the
  identity at an edge point, and the single edge over `0 < 1/2 < 1` and over `0 < 1` are at
  geometric distance `0`.
* **Symmetry.** Transport commutes with symmetry on the midpoint witness, and
  `d_geo(P, edge) = 1/2`.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4. Only the statement shape of
**Definition 4.36** is attributed: an `ε`-interleaving of Reeb graphs as a pair `A → U_ε B`,
`B → U_ε A` whose shifted composites through `U_ε U_ε ≅ U_(ε+ε)` are the units. The distance as an
infimum of parameters is attributed in the shape of **Definition 4.4**. Both are **proved here
independently** on `RGraphCat`. The comparison `d_cosheaf ≤ d_geo`, the transport
`cosheafShiftMap`, unit coherence and the thin-target lemma are library statements; none is
attributed to a numbered source result.

Not claimed here: the reverse inequality `d_geo ≤ d_cosheaf`; composition of geometric
interleavings and the triangle inequality for `d_geo`; enlargement along `ε ≤ ε'`;
nonexpansiveness of `U_ε` for `d_geo` and `d_geo(A, U_ε A) ≤ ε`; a comparison with Mapper;
absorption beyond (H2); a lift of `smoothingCompIso` to constructible cosheaves.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4, Definition
4.36](https://arxiv.org/html/1501.04147v1).
