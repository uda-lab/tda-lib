import TDA.Sheaf.OrthantSheaf
import TDA.Sheaf.StrictBasisLocalization
import TDA.Sheaf.RayLocalization

/-!
# Orthant sheaves as a localization; comparison with ray sheaves

This module applies `TDA.Sheaf.StrictBasisLocalization` to `orthantBasis n` of
`TDA.Sheaf.OrthantSheaf`, and compares the case `n = 1` with the ray sheaves of
`TDA.Sheaf.RaySheaf` and `TDA.Sheaf.RayLocalization`. The value category is `C : Type u` with
`[Category.{0} C]`, `[HasLimits C]` for `Q`, `[HasZeroMorphisms C]` for the ephemeral diagrams
and `[Abelian C]` for the Serre localization.

* `(orthantBasis n).adjunction C : Q ⊣ B`, `(orthantBasis n).BFullyFaithful C`,
  `Q_isLocalization`, exactness of `Q`, the Serre class `(orthantBasis n).ephemeral C` and
  `(orthantBasis n).localizationEquivalence C` are the general statements.
  `ephemeral_orthantBasis_iff`: a diagram is ephemeral when all its all-strict maps
  `M(x ≤ y)`, `∀ i, x i < y i`, vanish; `isZero_orthantQ_iff`: these are exactly the diagrams
  that `Q` kills.
* `RaySheaf.rayStrictBasis : StrictBasis ℝ raySpace` is the ray basis of `TDA.Sheaf.RaySheaf`;
  its `B`, `Q`, projections, unit and ephemeral class are `rayB`, `rayQ`, `rayProj`, `rayUnit`
  and `rayEphemeral` by definition (`rayStrictBasis_B`, `rayStrictBasis_Q`,
  `rayStrictBasis_proj`, `rayStrictBasis_unit`, `rayStrictBasis_ephemeral`).
* `n = 1`: `orthantOneRayHomeo` identifies the orthant space of `Fin 1 → ℝ` with the ray space,
  and `orthantOneRayBasisIso` the two bases along `OrderIso.funUnique (Fin 1) ℝ`. Hence
  `orthantOneRayBIso` (the orthant `B` is `rayB` of the pushforward, reindexed),
  `orthantOneRayQIso` (pushing forward the orthant `Q M` gives `rayQ` of `M` read on `ℝ`) and
  `orthantOne_ephemeral_iff` (the ephemeral classes correspond).
* `n = 0`: the all-strict order is the full relation (`strict_orthantBasis_zero`), so `Q` is an
  equivalence (`orthantQ_zero_isEquivalence`) and only zero diagrams are ephemeral
  (`ephemeral_orthantBasis_zero_iff`). For `0 < n` no point is strictly above itself
  (`not_strict_orthantBasis_self`).

`TDA.Sheaf.OrthantLocalizationExamples` checks a diagram on a horizontal line of the plane that
`Q` kills and a half-plane diagram that it does not.

Diagrams on `Fin n → ℝ` use the coordinatewise preorder category
`TDA.Persistence.realCoordinatePreorderCategory`, selected by `open scoped TDA.Persistence`;
outside that scope `Category (Fin n → ℝ)` is Mathlib's product category `CategoryTheory.pi`, and
the maps of a `PModule` on `Fin n → ℝ` are written through `TDA.Persistence.structureMap`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace Topology TopCat
open scoped TDA.Persistence

namespace TDA.Sheaf

/-! ## The ray basis -/

namespace RaySheaf

/-- The open rays as a strict basis of the ray space: the strict order is `<`, two rays meet
in the ray at the larger endpoint, and the midpoint interpolates. -/
noncomputable def rayStrictBasis : StrictBasis ℝ raySpace where
  ι := rayId
  U := ray
  antitone := ray_antitone
  le_of_mem h := le_of_lt h
  U_le := ray_le
  exists_mem := exists_ray_mem
  inf_le s t := (ray_inf s t).le
  interpolate {t s} h := by
    have hts : t < s := h
    refine ⟨(t + s) / 2, ?_, ?_⟩
    · change t < (t + s) / 2
      linarith
    · change (t + s) / 2 < s
      linarith

/-- The strict order of the ray basis is `<`. -/
theorem rayStrictBasis_strict_iff {s t : ℝ} : rayStrictBasis.Strict s t ↔ s < t :=
  Iff.rfl

/-- The `B` of the ray basis is `rayB`. -/
theorem rayStrictBasis_B (C : Type u) [Category.{0} C] : rayStrictBasis.B C = rayB C :=
  rfl

/-- The `Q` of the ray basis is `rayQ`. -/
theorem rayStrictBasis_Q (C : Type u) [Category.{0} C] [HasLimits C] :
    rayStrictBasis.Q C = rayQ C :=
  rfl

/-- The projections of the ray basis are `rayProj`. -/
theorem rayStrictBasis_proj {C : Type u} [Category.{0} C] [HasLimits C] (M : ℝ ⥤ C)
    {t s : ℝ} (h : t < s) : rayStrictBasis.proj M h = rayProj M h :=
  rfl

/-- The unit of the ray basis is `rayUnit`. -/
theorem rayStrictBasis_unit (C : Type u) [Category.{0} C] [HasLimits C] :
    rayStrictBasis.unit C = rayUnit C :=
  rfl

/-- The ephemeral class of the ray basis is `rayEphemeral`. -/
theorem rayStrictBasis_ephemeral (C : Type u) [Category.{0} C] [HasZeroMorphisms C] :
    rayStrictBasis.ephemeral C = rayEphemeral C :=
  rfl

end RaySheaf

namespace OrthantSheaf

open WithOrthant RaySheaf

variable {n : ℕ}

/-! ## The kernel of `Q` -/

section Kernel

variable {C : Type u} [Category.{0} C] [HasZeroMorphisms C]

/-- The orthant-ephemeral diagrams: all maps `M(x ≤ y)` with `x i < y i` for all `i` vanish. -/
theorem ephemeral_orthantBasis_iff (M : (Fin n → ℝ) ⥤ C) :
    (orthantBasis n).ephemeral C M ↔
      ∀ (x y : Fin n → ℝ) (h : ∀ i, x i < y i), M.map (homOfLE fun i => (h i).le) = 0 :=
  Iff.rfl

/-- `Q M` is zero exactly when all all-strict maps of `M` vanish. -/
theorem isZero_orthantQ_iff [HasLimits C] (M : (Fin n → ℝ) ⥤ C) :
    IsZero (((orthantBasis n).Q C).obj M) ↔
      ∀ (x y : Fin n → ℝ) (h : ∀ i, x i < y i), M.map (homOfLE fun i => (h i).le) = 0 :=
  ((orthantBasis n).ephemeral_iff M).symm

end Kernel

/-! ## `n = 1`: comparison with ray sheaves -/

section One

/-- The orthant space of `Fin 1 → ℝ` is the ray space: `x ↦ x 0`, with inverse the constant
family. -/
noncomputable def orthantOneRayHomeo : WithOrthant 1 ≃ₜ WithUpper ℝ where
  toFun x := WithUpper.toUpper (ofOrthant x 0)
  invFun y := toOrthant fun _ => WithUpper.ofUpper y
  left_inv x := by
    change (fun _ : Fin 1 => ofOrthant x 0) = ofOrthant x
    funext i
    rw [Subsingleton.elim i 0]
  right_inv _ := rfl
  continuous_toFun := by
    rw [continuous_def]
    intro V hV
    let V' : Opens raySpace := ⟨V, hV⟩
    refine ⟨fun a b hab ha => (isUpperSet_isOpen_toUpper_preimage V').1 (hab 0) ha,
      fun s hs => ?_⟩
    obtain ⟨p, hp, hsp⟩ := exists_ray_mem (V := V') hs
    have hsp' : p < s 0 := hsp
    refine ⟨s 0 - p, sub_pos.2 hsp', ?_⟩
    change WithUpper.toUpper (s 0 - (s 0 - p)) ∈ V
    rw [sub_sub_cancel]
    exact hp
  continuous_invFun := by
    rw [continuous_def]
    rintro S ⟨hup, hstep⟩
    change IsOpen (WithUpper.ofUpper ⁻¹' {t : ℝ | toOrthant (fun _ => t) ∈ S})
    refine (isOpen_ofUpper_preimage_iff _).2 ⟨fun a b hab ha => hup (fun _ => hab) ha, ?_⟩
    refine isOpen_iff_forall_mem_open.2 fun t ht => ?_
    obtain ⟨δ, hδ, h⟩ := hstep _ ht
    refine ⟨Set.Ioi (t - δ), fun u hu => hup (fun _ => le_of_lt hu) h, isOpen_Ioi, ?_⟩
    change t - δ < t
    linarith

/-- The orthant space of `Fin 1 → ℝ` and the ray space are isomorphic in `TopCat`. -/
noncomputable def orthantOneRayIso : orthantSpace 1 ≅ raySpace :=
  TopCat.isoOfHomeo orthantOneRayHomeo

@[simp]
theorem orthantOneRayIso_hom_apply (x : WithOrthant 1) :
    orthantOneRayIso.hom x = WithUpper.toUpper (ofOrthant x 0) :=
  rfl

/-- The orthant basis of `Fin 1 → ℝ` and the ray basis are isomorphic along
`OrderIso.funUnique (Fin 1) ℝ`: the orthant at `p` is the preimage of the ray at `p 0`. -/
noncomputable def orthantOneRayBasisIso : (orthantBasis 1).Iso rayStrictBasis where
  orderIso := OrderIso.funUnique (Fin 1) ℝ
  homeo := orthantOneRayIso
  hom_ι _ := rfl
  map_U p := by
    ext x
    change p 0 < ofOrthant x 0 ↔ ∀ i, p i < ofOrthant x i
    rw [Fin.forall_fin_one]

variable (C : Type u) [Category.{0} C]

/-- `n = 1`, the functor `B`: the orthant `B F` is `rayB` of the pushforward of `F` to the ray
space, read on `Fin 1 → ℝ`. -/
noncomputable def orthantOneRayBIso :
    (orthantBasis 1).B C ≅ TopCat.Sheaf.pushforward C orthantOneRayIso.hom ⋙ rayB C ⋙
      (Functor.whiskeringLeft (Fin 1 → ℝ) ℝ C).obj
        (OrderIso.funUnique (Fin 1) ℝ).monotone.functor :=
  orthantOneRayBasisIso.BIso C

@[simp]
theorem orthantOneRayBIso_hom_app_app (F : (orthantSpace 1).Sheaf C) (p : Fin 1 → ℝ) :
    ((orthantOneRayBIso C).hom.app F).app p =
      F.presheaf.map (homOfLE (orthantOneRayBasisIso.map_U p).le).op :=
  rfl

/-- `n = 1`, the functor `Q`: the pushforward to the ray space of the orthant `Q M` is `rayQ`
of `M` read on `ℝ` through the constant families. -/
noncomputable def orthantOneRayQIso [HasLimits C] :
    (orthantBasis 1).Q C ⋙ TopCat.Sheaf.pushforward C orthantOneRayIso.hom ≅
      (Functor.whiskeringLeft ℝ (Fin 1 → ℝ) C).obj
        (OrderIso.funUnique (Fin 1) ℝ).symm.monotone.functor ⋙ rayQ C :=
  orthantOneRayBasisIso.QIso C

variable {C}

/-- `n = 1`, the ephemeral classes: a diagram `M` on `ℝ` is ray-ephemeral exactly when `M`
read on `Fin 1 → ℝ` is orthant-ephemeral. -/
theorem orthantOne_ephemeral_iff [HasZeroMorphisms C] (M : ℝ ⥤ C) :
    (orthantBasis 1).ephemeral C ((OrderIso.funUnique (Fin 1) ℝ).monotone.functor ⋙ M) ↔
      rayEphemeral C M :=
  orthantOneRayBasisIso.ephemeral_iff M

end One

/-! ## `n = 0`: the identity case -/

section Zero

/-- For `n = 0` the all-strict order is the full relation: there is no coordinate. -/
theorem strict_orthantBasis_zero (x y : Fin 0 → ℝ) : (orthantBasis 0).Strict x y :=
  fun i => i.elim0

/-- For `0 < n` no point is strictly above itself. -/
theorem not_strict_orthantBasis_self (hn : 0 < n) (x : Fin n → ℝ) :
    ¬ (orthantBasis n).Strict x x :=
  fun h => lt_irrefl _ (h ⟨0, hn⟩)

/-- For `n = 0`, `Q` is an equivalence. -/
theorem orthantQ_zero_isEquivalence (C : Type u) [Category.{0} C] [HasLimits C] :
    ((orthantBasis 0).Q C).IsEquivalence :=
  (orthantBasis 0).Q_isEquivalence_of_strict_refl fun x => strict_orthantBasis_zero x x

/-- For `n = 0`, only the zero diagrams are ephemeral. -/
theorem ephemeral_orthantBasis_zero_iff {C : Type u} [Category.{0} C] [HasZeroMorphisms C]
    (M : (Fin 0 → ℝ) ⥤ C) : (orthantBasis 0).ephemeral C M ↔ IsZero M :=
  (orthantBasis 0).ephemeral_iff_isZero_of_strict_refl (fun x => strict_orthantBasis_zero x x) M

end Zero

end OrthantSheaf

end TDA.Sheaf
