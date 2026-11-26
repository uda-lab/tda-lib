import TDA.Sheaf.RaySheaf
import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Topology.Sheaves.Limits

/-!
# Ray sheaves as the localization of persistence modules at ephemeral modules

This module continues `TDA.Sheaf.RaySheaf`, with `rayQ C : (ℝ ⥤ C) ⥤ raySpace.Sheaf C` and
`rayB C : raySpace.Sheaf C ⥤ (ℝ ⥤ C)`. The value category is `C : Type u` with
`[Category.{0} C] [HasLimits C]`; the ephemeral diagrams use `[HasZeroMorphisms C]`, and the
Serre localization uses `[Abelian C]`. The abelian structure of `ℝ ⥤ C` is Mathlib's
`functorCategoryAbelian`.

* `rayAdjunction C : rayQ C ⊣ rayB C` has unit `rayUnit C` and counit `(rayCounitIso C).hom`
  (`rayAdjunction_unit`, `rayAdjunction_counit`); a map `Q M ⟶ F` corresponds to `η_M`
  followed by its `B` image, and a map `M ⟶ B F` to its `Q` image followed by the counit
  (`rayAdjunction_homEquiv_apply`, `rayAdjunction_homEquiv_symm_apply`). The triangles are
  checked on the limit projections `rayProj` and the restrictions to rays.
* `rayBFullyFaithful C`: `B` is fully faithful, since the counit is an isomorphism.
* `rayQ_isLocalization`: `Q` is a localization functor at the morphisms it inverts, by
  Mathlib's `Adjunction.isLocalization`.
* `rayQ_preservesLimits` (pushforward of sheaves is computed on presheaves, after the Alexandrov
  equivalence) and `rayQ_preservesColimits` (as a left adjoint): `Q` is exact.
* `rayEphemeral C`: the diagrams whose strict maps `M(s ≤ t)`, `s < t`, are all zero.
  `rayEphemeral_iff`: `M` is ephemeral exactly when `Q M` is zero, so `rayEphemeral C` is the
  kernel of `Q` (`rayEphemeral_eq_kernel`). `isZero_rayB_iff`: `B F` is zero exactly when `F` is.
* For abelian `C`, `raySheafAbelian C` is the abelian structure on ray sheaves obtained from
  `Q ⊣ B` and `QB ≅ 𝟭` by `abelianOfAdjunction`; the ephemeral diagrams form a Serre class
  (`rayEphemeral_isSerreClass`).
* `rayEphemeral_isoModSerre`: the morphisms inverted by `Q` are `(rayEphemeral C).isoModSerre`,
  so `isIso_rayQ_map_iff`: `Q f` is an isomorphism exactly when `kernel f` and `cokernel f` are
  ephemeral. `rayQ_isLocalization_isoModSerre`: `Q` is a localization functor at
  `(rayEphemeral C).isoModSerre`, and `rayLocalizationEquivalence C` compares Mathlib's
  localization `(rayEphemeral C).isoModSerre.Localization` with `raySpace.Sheaf C`, compatibly
  with `Q` (`rayLocalizationEquivalenceCompIso`).

`TDA.Sheaf.RayLocalizationExamples` checks an endpoint alteration that `Q` inverts, a positive
interval with nonzero image and an ephemeral singleton.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace Topology TopCat

namespace TDA.Sheaf.RaySheaf

noncomputable section

section Adjunction

variable (C : Type u) [Category.{0} C] [HasLimits C]

/-- The right triangle at `F`: `η_{B F}` followed by `B(ε_F)` is the identity. -/
private theorem rayUnit_app_rayB_comp (F : raySpace.Sheaf C) :
    (rayUnit C).app ((rayB C).obj F) ≫ (rayB C).map ((rayCounitIso C).hom.app F) = 𝟙 _ := by
  have h : (rayUnit C).app ((rayB C).obj F) = (rayB C).map ((rayCounitIso C).inv.app F) := by
    ext t
    exact rayProj_ext _ fun s hs =>
      (rayUnit_app_app_rayProj _ hs).trans (rayCounitIso_inv_app_hom_app_rayProj F hs).symm
  rw [h, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (rayB C).map_id F

/-- The left triangle at `M`: `Q(η_M)` followed by `ε_{Q M}` is the identity. -/
private theorem rayQ_map_rayUnit_comp (M : ℝ ⥤ C) :
    (rayQ C).map ((rayUnit C).app M) ≫ (rayCounitIso C).hom.app ((rayQ C).obj M) = 𝟙 _ := by
  have h : (rayQ C).map ((rayUnit C).app M) = (rayCounitIso C).inv.app ((rayQ C).obj M) := by
    apply (rayB C).map_injective
    ext t
    refine rayProj_ext _ fun s hs => ?_
    refine (map_app_rayProj ((rayUnit C).app M) hs).trans
      (Eq.trans ?_ (rayCounitIso_inv_app_hom_app_rayProj ((rayQ C).obj M) hs).symm)
    refine rayProj_ext M fun s' hs' => ?_
    refine ((Category.assoc _ _ _).trans
      ((congrArg (rayProj M hs ≫ ·) (rayUnit_app_app_rayProj M hs')).trans
        (rayProj_comp_map M hs _))).trans ?_
    exact (map_rayProj M (homOfLE hs.le) hs').symm
  rw [h]
  exact Iso.inv_hom_id_app _ _

/-- The adjunction `Q ⊣ B`, with unit `rayUnit` and counit `rayCounitIso.hom`. -/
def rayAdjunction : rayQ C ⊣ rayB C :=
  Adjunction.mkOfUnitCounit
    { unit := rayUnit C
      counit := (rayCounitIso C).hom
      left_triangle := by
        refine NatTrans.ext (funext fun M => ?_)
        simpa using rayQ_map_rayUnit_comp C M
      right_triangle := by
        refine NatTrans.ext (funext fun F => ?_)
        simpa using rayUnit_app_rayB_comp C F }

@[simp]
theorem rayAdjunction_unit : (rayAdjunction C).unit = rayUnit C :=
  rfl

@[simp]
theorem rayAdjunction_counit : (rayAdjunction C).counit = (rayCounitIso C).hom :=
  rfl

variable {C}

/-- A map `Q M ⟶ F` corresponds to `η_M` followed by its image under `B`. -/
theorem rayAdjunction_homEquiv_apply (M : ℝ ⥤ C) (F : raySpace.Sheaf C)
    (φ : (rayQ C).obj M ⟶ F) :
    (rayAdjunction C).homEquiv M F φ = (rayUnit C).app M ≫ (rayB C).map φ :=
  Adjunction.homEquiv_unit _ _ _ _

/-- A map `M ⟶ B F` corresponds to its image under `Q` followed by the counit. -/
theorem rayAdjunction_homEquiv_symm_apply (M : ℝ ⥤ C) (F : raySpace.Sheaf C)
    (ψ : M ⟶ (rayB C).obj F) :
    ((rayAdjunction C).homEquiv M F).symm ψ = (rayQ C).map ψ ≫ (rayCounitIso C).hom.app F :=
  Adjunction.homEquiv_counit _ _ _ _

variable (C)

/-- `B` is fully faithful: the counit of `Q ⊣ B` is the isomorphism `rayCounitIso`. -/
def rayBFullyFaithful : (rayB C).FullyFaithful :=
  haveI : IsIso (rayAdjunction C).counit := (inferInstance : IsIso (rayCounitIso C).hom)
  (rayAdjunction C).fullyFaithfulROfIsIsoCounit

/-- `B` is full. -/
instance rayB_full : (rayB C).Full :=
  (rayBFullyFaithful C).full

/-- `Q` is a localization functor at the morphisms that it inverts. -/
instance rayQ_isLocalization :
    (rayQ C).IsLocalization ((MorphismProperty.isomorphisms _).inverseImage (rayQ C)) :=
  (rayAdjunction C).isLocalization

/-- `Q` preserves limits: pushforward of sheaves is computed on presheaves, and the Alexandrov
sheaf functor is an equivalence. -/
instance rayQ_preservesLimits : PreservesLimits (rayQ C) := by
  have : PreservesLimits (TopCat.Presheaf.pushforward C rayId) :=
    inferInstanceAs (PreservesLimits ((Functor.whiskeringLeft _ _ C).obj (Opens.map rayId).op))
  have : PreservesLimits (TopCat.Sheaf.pushforward C rayId ⋙ TopCat.Sheaf.forget C raySpace) :=
    inferInstanceAs
      (PreservesLimits (TopCat.Sheaf.forget C _ ⋙ TopCat.Presheaf.pushforward C rayId))
  have : PreservesLimits (TopCat.Sheaf.pushforward C rayId) :=
    preservesLimits_of_reflects_of_preserves _ (TopCat.Sheaf.forget C raySpace)
  unfold rayQ
  infer_instance

/-- `Q` preserves colimits, as the left adjoint of `B`. -/
instance rayQ_preservesColimits : PreservesColimits (rayQ C) :=
  (rayAdjunction C).leftAdjoint_preservesColimits

example : PreservesFiniteLimits (rayQ C) := inferInstance
example : PreservesFiniteColimits (rayQ C) := inferInstance

end Adjunction

/-! ## Ephemeral modules -/

section Ephemeral

variable (C : Type u) [Category.{0} C]

/-- The ephemeral diagrams: every strict map `M(s ≤ t)` with `s < t` is zero. -/
def rayEphemeral [HasZeroMorphisms C] : ObjectProperty (ℝ ⥤ C) :=
  fun M => ∀ (s t : ℝ) (h : s < t), M.map (homOfLE h.le) = 0

variable {C} [HasZeroMorphisms C] [HasLimits C]

/-- A sheaf on the ray space is zero exactly when its values on rays are. -/
theorem isZero_rayB_iff (F : raySpace.Sheaf C) : IsZero ((rayB C).obj F) ↔ IsZero F := by
  refine ⟨IsZero.of_full_of_faithful_of_isZero (rayB C) F, fun h => ?_⟩
  have : PreservesLimits (rayB C) := (rayAdjunction C).rightAdjoint_preservesLimits
  exact (IsZero.iff_id_eq_zero _).2 ((h.isTerminal.isTerminalObj (rayB C) F).hom_ext _ _)

/-- `Q M` is zero exactly when `M` is ephemeral. -/
theorem rayEphemeral_iff (M : ℝ ⥤ C) : rayEphemeral C M ↔ IsZero ((rayQ C).obj M) := by
  rw [← isZero_rayB_iff]
  constructor
  · intro h
    refine Functor.isZero _ fun t => (IsZero.iff_id_eq_zero _).2 ?_
    refine rayProj_ext M fun s hs => ?_
    have hr : t < (t + s) / 2 := by linarith
    have hrs : (t + s) / 2 < s := by linarith
    rw [Category.id_comp, zero_comp, ← rayProj_comp_map M hr (homOfLE hrs.le), h _ _ hrs,
      comp_zero]
  · intro hz s t h
    rw [← rayUnit_app_app_rayProj M h, hz.eq_of_tgt ((rayUnit C).app M) 0]
    exact zero_comp

/-- The ephemeral diagrams are the kernel of `Q`. -/
theorem rayEphemeral_eq_kernel : rayEphemeral C = (rayQ C).kernel := by
  funext M
  exact propext (rayEphemeral_iff M)

end Ephemeral

/-! ## The Serre localization -/

section Serre

variable (C : Type u) [Category.{0} C] [Abelian C] [HasLimits C]

/-- The category of sheaves on the ray space is abelian, transported along `Q ⊣ B` with
`QB ≅ 𝟭` (`abelianOfAdjunction`). -/
@[instance_reducible]
def raySheafAbelian : Abelian (raySpace.Sheaf C) :=
  letI : Preadditive (raySpace.Sheaf C) :=
    inferInstanceAs (Preadditive (CategoryTheory.Sheaf (Opens.grothendieckTopology raySpace) C))
  letI : (rayQ C).IsLeftAdjoint := (rayAdjunction C).isLeftAdjoint
  abelianOfAdjunction (rayB C) (rayQ C) (rayCounitIso C) (rayAdjunction C)

/-- The ephemeral diagrams form a Serre class. -/
instance rayEphemeral_isSerreClass : (rayEphemeral C).IsSerreClass := by
  let _ := raySheafAbelian C
  rw [rayEphemeral_eq_kernel]
  infer_instance

/-- The morphisms inverted by `Q` are the isomorphisms modulo ephemeral diagrams. -/
theorem rayEphemeral_isoModSerre :
    (rayEphemeral C).isoModSerre = (MorphismProperty.isomorphisms _).inverseImage (rayQ C) := by
  let _ := raySheafAbelian C
  have key : ∀ (P : ObjectProperty (ℝ ⥤ C)) [P.IsSerreClass], P = (rayQ C).kernel →
      P.isoModSerre = (MorphismProperty.isomorphisms _).inverseImage (rayQ C) := by
    rintro P _ rfl
    exact Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms (rayQ C)
  exact key _ (rayEphemeral_eq_kernel)

variable {C}

/-- `Q` inverts `f` exactly when the kernel and the cokernel of `f` are ephemeral. -/
theorem isIso_rayQ_map_iff {M N : ℝ ⥤ C} (f : M ⟶ N) :
    IsIso ((rayQ C).map f) ↔ rayEphemeral C (kernel f) ∧ rayEphemeral C (cokernel f) := by
  have h := congrArg (fun W : MorphismProperty (ℝ ⥤ C) => W f) (rayEphemeral_isoModSerre C)
  exact (iff_of_eq h).symm

variable (C)

/-- `Q` is a localization functor at the isomorphisms modulo ephemeral diagrams. -/
instance rayQ_isLocalization_isoModSerre : (rayQ C).IsLocalization (rayEphemeral C).isoModSerre :=
  (rayEphemeral_isoModSerre C) ▸ rayQ_isLocalization C

/-- The comparison of Mathlib's localization at the isomorphisms modulo ephemeral diagrams with
sheaves on the ray space. -/
def rayLocalizationEquivalence :
    (rayEphemeral C).isoModSerre.Localization ≌ raySpace.Sheaf C :=
  Localization.uniq (rayEphemeral C).isoModSerre.Q (rayQ C) (rayEphemeral C).isoModSerre

/-- The comparison is compatible with the localization functor and `Q`. -/
def rayLocalizationEquivalenceCompIso :
    (rayEphemeral C).isoModSerre.Q ⋙ (rayLocalizationEquivalence C).functor ≅ rayQ C :=
  Localization.compUniqFunctor _ _ _

end Serre

end

end TDA.Sheaf.RaySheaf
