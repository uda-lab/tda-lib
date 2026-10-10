import TDA.Reeb.IntervalComponents
import TDA.Reeb.Smoothing

/-!
# Uniform perturbation gives an explicit component interleaving

For continuous `f g : C(X, ℝ)` on the same space and `ε : ℝ≥0` with the pointwise bound
`∀ x, |f x - g x| ≤ ε`, every inverse image `f ⁻¹' I` is contained in `g ⁻¹' T_ε I`
(`preimage_subset_preimage_thicken`). The continuous inclusion of subspaces, with identity point
map, induces on path components the witness `φ : C_f|Int ⟶ S_ε (C_g|Int)`; the reverse witness
`ψ` is the same construction for the swapped bound. Both interleaving triangles hold on
representatives, so `perturbationInterleaving` is an explicit `ε`-interleaving of the interval
restrictions (de Silva–Munch–Patel, Theorem 4.6(i) and its proof, in pointwise form).

The bound is stated pointwise, without a supremum. The construction is compatible with the
interleaving laws: at `f = g` it is the identity interleaving at every parameter, at parameter
`0` its isomorphism is the identity, and symmetry, enlargement and composition correspond to the
swapped, weakened and triangle-inequality bounds. No cosheaf condition and no Reeb quotient is
used. See `docs/math/reeb-perturbation.md`.
-/

open Set CategoryTheory
open scoped NNReal

universe u

namespace TDA.Reeb

open OpenInterval

section Perturbation

variable {X : Type u} [TopologicalSpace X]

/-- Pointwise inclusion: `a ∈ I` and `|b - a| ≤ ε` give `b ∈ T_ε I` (witness `a`). -/
theorem mem_thicken_of_abs_sub_le {ε : ℝ≥0} {I : OpenInterval} {a b : ℝ} (ha : a ∈ I)
    (h : |b - a| ≤ ε) : b ∈ thicken ε I :=
  mem_thicken.2 ⟨a, ha, h⟩

/-- `f ⁻¹' I ⊆ g ⁻¹' T_ε I` under the pointwise bound (DMP, proof of Theorem 4.6). -/
theorem preimage_subset_preimage_thicken {f g : C(X, ℝ)} {ε : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) (I : OpenInterval) :
    f ⁻¹' (I : Set ℝ) ⊆ g ⁻¹' (thicken ε I : Set ℝ) := fun x hx =>
  mem_thicken_of_abs_sub_le hx ((abs_sub_comm _ _).trans_le (hfg x))

/-- The bound is symmetric. -/
theorem perturbationBound_symm {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε) :
    ∀ x, |g x - f x| ≤ ε := fun x =>
  (abs_sub_comm _ _).trans_le (hfg x)

/-- The continuous inclusion `f ⁻¹ I → g ⁻¹ T_ε I` (identity on points). -/
def perturbationInclusion {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε)
    (I : OpenInterval) : C({x : X // f x ∈ toOpens I}, {x : X // g x ∈ toOpens (thicken ε I)}) where
  toFun x := ⟨x.1, preimage_subset_preimage_thicken hfg I x.2⟩
  continuous_toFun := by fun_prop

/-- The inclusion is mathlib's `ContinuousMap.inclusion` on the inverse-image sets. -/
theorem perturbationInclusion_eq_inclusion {f g : C(X, ℝ)} {ε : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) (I : OpenInterval) :
    perturbationInclusion hfg I =
      ContinuousMap.inclusion (s := f ⁻¹' (I : Set ℝ)) (t := g ⁻¹' (thicken ε I : Set ℝ))
        (preimage_subset_preimage_thicken hfg I) := rfl

/-- The witness `φ : C_f|Int ⟶ S_ε (C_g|Int)`, componentwise `componentMap` of the inclusion. -/
def perturbationNatTrans {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε) :
    intervalComponents f ⟶ (smoothing ε).obj (intervalComponents g) where
  app I := TypeCat.ofHom (componentMap (perturbationInclusion hfg I))
  naturality I J i := by
    ext c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

@[simp]
theorem perturbationNatTrans_app_mk {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε)
    (I : OpenInterval) (x : {x : X // f x ∈ toOpens I}) :
    (perturbationNatTrans hfg).app I (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨x.1, preimage_subset_preimage_thicken hfg I x.2⟩ :
        {x : X // g x ∈ toOpens (thicken ε I)}) := rfl

/-- Bridge: the component at `I` is `componentMap` of the inclusion. -/
theorem perturbationNatTrans_app_apply {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε)
    (I : OpenInterval) (c : (intervalComponents f).obj I) :
    (perturbationNatTrans hfg).app I c = componentMap (perturbationInclusion hfg I) c := rfl

/-- **Uniform perturbation** (DMP Theorem 4.6(i), pointwise form): `∀ x, |f x - g x| ≤ ε`
gives an explicit `ε`-interleaving of `C_f|Int` and `C_g|Int`. -/
def perturbationInterleaving {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε) :
    Interleaving ε (intervalComponents f) (intervalComponents g) :=
  Interleaving.ofApp (perturbationNatTrans hfg)
    (perturbationNatTrans (perturbationBound_symm hfg))
    (fun I => by
      ext c
      induction c using ZerothHomotopy.rec with
      | mk x => rfl)
    (fun I => by
      ext c
      induction c using ZerothHomotopy.rec with
      | mk x => rfl)

@[simp]
theorem perturbationInterleaving_φ {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε) :
    (perturbationInterleaving hfg).φ = perturbationNatTrans hfg := rfl

@[simp]
theorem perturbationInterleaving_ψ {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε) :
    (perturbationInterleaving hfg).ψ = perturbationNatTrans (perturbationBound_symm hfg) := rfl

/-- Existence form, for the interleaving distance. -/
theorem nonempty_interleaving_of_abs_sub_le {f g : C(X, ℝ)} {ε : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) :
    Nonempty (Interleaving ε (intervalComponents f) (intervalComponents g)) :=
  ⟨perturbationInterleaving hfg⟩

/-- `f = g`: the perturbation witnesses are the identity (unit) witnesses at every `ε`. -/
theorem perturbationInterleaving_self (f : C(X, ℝ)) {ε : ℝ≥0} (h : ∀ x, |f x - f x| ≤ ε) :
    perturbationInterleaving h = Interleaving.refl ε (intervalComponents f) := by
  ext I c
  · induction c using ZerothHomotopy.rec with
    | mk x => rfl
  · induction c using ZerothHomotopy.rec with
    | mk x => rfl

/-- `f = g` at `ε = 0`: the associated natural isomorphism is the identity. -/
theorem perturbationInterleaving_self_toIso (f : C(X, ℝ)) (h : ∀ x, |f x - f x| ≤ (0 : ℝ≥0)) :
    (perturbationInterleaving h).toIso = Iso.refl (intervalComponents f) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Symmetry is the swapped bound. -/
theorem perturbationInterleaving_symm {f g : C(X, ℝ)} {ε : ℝ≥0} (hfg : ∀ x, |f x - g x| ≤ ε) :
    (perturbationInterleaving hfg).symm = perturbationInterleaving (perturbationBound_symm hfg) :=
  rfl

/-- Enlargement is the weakened bound. -/
theorem perturbationInterleaving_mono {f g : C(X, ℝ)} {ε ε' : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) (h : ε ≤ ε') :
    (perturbationInterleaving hfg).mono h =
      perturbationInterleaving (fun x => (hfg x).trans (by exact_mod_cast h)) := by
  ext I c
  · induction c using ZerothHomotopy.rec with
    | mk x => rfl
  · induction c using ZerothHomotopy.rec with
    | mk x => rfl

/-- Composition is the triangle-inequality bound. -/
theorem perturbationInterleaving_trans {f g h : C(X, ℝ)} {ε δ : ℝ≥0}
    (hfg : ∀ x, |f x - g x| ≤ ε) (hgh : ∀ x, |g x - h x| ≤ δ)
    (hfh : ∀ x, |f x - h x| ≤ (ε + δ : ℝ≥0)) :
    (perturbationInterleaving hfg).trans (perturbationInterleaving hgh) =
      perturbationInterleaving hfh := by
  ext I c
  · induction c using ZerothHomotopy.rec with
    | mk x => rfl
  · induction c using ZerothHomotopy.rec with
    | mk x => rfl

end Perturbation

end TDA.Reeb
