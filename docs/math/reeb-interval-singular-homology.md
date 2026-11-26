# Degree-zero singular homology of interval preimages

## Setting

Let `X` be a topological space in `Type u`, `f : C(X, ℝ)` and `k` a ring in `Type u`. Write
`k₀ = ModuleCat.of k k`, so that all coproducts below live in `ModuleCat.{u} k`.
`OpenInterval` is the thin category of open order-convex subsets of `ℝ` ordered by inclusion.

- `intervalPreimageTopCat f : OpenInterval ⥤ TopCat.{u}` sends `I` to the subspace
  `{x // f x ∈ I}` and an inclusion `I ≤ J` to `preimageInclusion f` along the interval-to-opens
  functor `toOpensFunctor` (`intervalPreimageTopCat_map_hom` is `rfl`). Identity and composition
  hold because both sides are inclusions of subtypes.
- `intervalSingularHomology k n f` is `intervalPreimageTopCat f` followed by
  `((singularHomologyFunctor (ModuleCat k) n).obj k₀)`, Mathlib's `n`-th singular homology with
  coefficients `k₀`.
- `linearizedIntervalComponents k f` is `intervalComponents f ⋙ sigmaConst.obj k₀`: at `I`
  the coproduct `∐_{c ∈ π₀(f ⁻¹ I)} k₀`, with the coproduct maps induced by the maps of path
  components.

## The degree-zero comparison

`intervalSingularHomologyIso₀ k f : intervalSingularHomology k 0 f ≅ linearizedIntervalComponents k f`
has component `TopCat.singularHomology₀Iso (f ⁻¹ I) k₀` at `I`. No compactness, tameness,
local-connectedness or finiteness assumption is used, and `k` is any ring.

Naturality is proved once for an arbitrary continuous map `g : X ⟶ Y` of spaces:

```
H₀(g) ≫ (singularHomology₀Iso Y).hom
  = (singularHomology₀Iso X).hom ≫ (sigmaConst.obj k₀).map (componentMap g)
```

(`singularHomology₀Iso_hom_naturality`). Cancel the isomorphism at `X`, then test on the coproduct
injection indexed by a path component. Every path component is `ZerothHomotopy.mk x` for a point
`x`, and both sides send the class of `x` to the injection of `ZerothHomotopy.mk (g x)`. Mathlib's
`SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom` gives the left half; `ι_chainComplexMap_f`
and naturality of `homologyπ` and `liftCycles` give naturality of the classes. This replaces the
epimorphism `chain complex in degree 0 → H₀` by the surjectivity of `ZerothHomotopy.mk`, and needs
no property of the cokernel cofork of `SSet.homologyData₀` beyond what
`TopCat.singularHomology₀Iso` already packages.

The class of a point `x : f ⁻¹ I` is `singularHomology₀Class (f ⁻¹ I) k₀ x : k₀ ⟶ H₀(f ⁻¹ I)`, the
image of its `0`-simplex (`intervalClass`). For `i : I ⟶ J`:

- `intervalClass_comp_map`: `class x ≫ H₀(i) = class (incl x)`;
- `intervalClass_comp_intervalSingularHomologyIso₀_hom_app`: `class x ≫ iso.hom.app I` is the
  injection of `ZerothHomotopy.mk x`;
- `intervalClass_comp_map_comp_intervalSingularHomologyIso₀_hom_app` and
  `intervalClass_comp_intervalSingularHomologyIso₀_hom_app_comp_map`: both composites
  `class x ≫ H₀(i) ≫ iso.hom.app J` and `class x ≫ iso.hom.app I ≫ (linearized).map i` equal the
  injection indexed by `ZerothHomotopy.mk (incl x)`, the second by `intervalComponents_map_mk`.

## Perturbation stability

For `f g : C(X, ℝ)` with `∀ x, |f x - g x| ≤ ε`, every `f ⁻¹ I` lies in `g ⁻¹ T_ε I`, and the
inclusion is continuous (`perturbationInclusion`). Singular homology applied to it gives
`intervalSingularHomologyPerturbation k n h : H_n(f ⁻¹ I) ⟶ H_n(g ⁻¹ T_ε I)`, natural in `I`. The
reverse maps are those of the swapped bound. Both composites are induced by the subtype inclusion
`f ⁻¹ I ⊆ f ⁻¹ T_ε T_ε I`, which is the image of `thickenUnit`, so functoriality (and extensionality
of continuous maps on points) gives the two triangles, and `Interleaving.ofApp` the
`ε`-interleaving `intervalSingularHomologyInterleaving`. This holds in every degree, for every ring
and every space. The pointwise bound gives `d(H_n f, H_n g) ≤ ε`, and for arbitrary `f g` the
bound `d(H_n f, H_n g) ≤ ‖f − g‖∞ ∈ [0, ∞]`.

In degree zero the maps agree with the existing path-component witness. For one inclusion `j`,
`singularHomology₀Iso_hom_naturality` says `H₀(j) ≫ iso = iso ≫ linearized (componentMap j)`; at
`j = perturbationTopHom h I` this is `intervalSingularHomologyPerturbation_app_comp_iso₀`, and
`intervalSingularHomologyPerturbation_zero` conjugates the witness by `intervalSingularHomologyIso₀`
at `f` and `g`.

Sharpness on a point: for the constant maps from a point at heights `a` and `b` (a nontrivial ring
`k`), the distance is exactly `|a − b|`. If `ε < |a − b|`, choose an open interval `I` around `a`
whose `ε`-thickening omits `b`. The value of `g` on the thickening is zero, so the first composite
`H₀(f ⁻¹ I) ⟶ H₀(g ⁻¹ T_ε I) ⟶ H₀(f ⁻¹ T_ε T_ε I)` is zero, while the transition on `H₀` of the point
is an isomorphism, compatible with the augmentation to `k`. A zero isomorphism on a nonzero value is
impossible.

## Boundary

This is the degree-zero comparison only. The isomorphism forgets all higher homology and is not
a derived equivalence; it does not identify `H₀` with sections of a sheaf on `ℝ`. Higher degrees,
Mayer–Vietoris maps and derived direct images are separate results. The empty interval has zero
value on both sides (`isZero_intervalSingularHomology₀_obj_bot`,
`isZero_linearizedIntervalComponents_obj_bot`).

## Fixtures

`TDA.Reeb.IntervalSingularHomologyExamples`, over an arbitrary ring `k : Type`:

- the empty interval, and an empty source space (zero on every interval);
- the identity of `ℝ`: for a nonempty interval the preimage is path connected, so
  `H₀ ⟶ k₀` is an isomorphism and every inclusion with nonempty source induces an isomorphism;
- `f t = t²` with the narrow band `(1, 4)` and the wide band `(-1, 4)`. The preimage of `(1, 4)` is
  `(-2, -1) ∪ (1, 2)`, whose two path components are told apart by the sign of the point
  (`signEquiv`). The preimage of `(-1, 4)` is `(-2, 2)`, connected. `fold` shows that the inclusion
  induces, up to isomorphisms `H₀(f ⁻¹ (1,4)) ≅ ∐_{Bool} k₀` and `H₀(f ⁻¹ (-1,4)) ≅ k₀`, the
  codiagonal `Sigma.desc (fun _ => 𝟙 k₀)`, the fold `k ⊕ k ⟶ k`.

`TDA.Reeb.IntervalSingularHomologyStabilityExamples`: an empty source, parameter `0`, empty preimages
(`isZero_obj_of_preimage_empty`) and the constant maps from a point
(`interleavingDistance_const`, `isEmpty_interleaving_const`, `not_nonempty_iso_const`).
