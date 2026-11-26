import TDA.Sheaf.StrictBasis
import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Topology.Sheaves.Limits

/-!
# Sheaves on a strict basis as a localization

This module continues `TDA.Sheaf.StrictBasis` for `S : StrictBasis P X`, with
`S.Q C : (P ⥤ C) ⥤ X.Sheaf C` and `S.B C : X.Sheaf C ⥤ (P ⥤ C)`. The value category is
`C : Type u` with `[Category.{0} C] [HasLimits C]`; the ephemeral diagrams use
`[HasZeroMorphisms C]`, and the Serre localization uses `[Abelian C]`.

* `S.adjunction C : S.Q C ⊣ S.B C` has unit `S.unit C` and counit `(S.counitIso C).hom`
  (`adjunction_unit`, `adjunction_counit`, `adjunction_homEquiv_apply`,
  `adjunction_homEquiv_symm_apply`); `S.BFullyFaithful C`; `Q_isLocalization` (Mathlib's
  `Adjunction.isLocalization`); `Q_preservesLimits` and `Q_preservesColimits`: `Q` is exact.
* `S.ephemeral C`: the diagrams whose maps `M(s ≤ t)` with `S.Strict s t` all vanish.
  `ephemeral_iff`: `M` is ephemeral exactly when `Q M` is zero (`ephemeral_eq_kernel`);
  `isZero_B_iff`.
* For abelian `C`, `S.sheafAbelian C` is the abelian structure on `X.Sheaf C` from
  `abelianOfAdjunction`; `ephemeral_isSerreClass`, `ephemeral_isoModSerre` (the morphisms
  inverted by `Q`), `isIso_Q_map_iff`, `Q_isLocalization_isoModSerre`,
  `localizationEquivalence` and `localizationEquivalenceCompIso`.
* The identity case: when `Strict` is reflexive, the unit is an isomorphism
  (`isIso_unit_app_app_of_strict_refl`), `Q` is an equivalence
  (`Q_isEquivalence_of_strict_refl`) and the ephemeral diagrams are the zero diagrams
  (`ephemeral_iff_isZero_of_strict_refl`).
* Comparison: `sheafPushforwardEquivalence C h` is pushforward along an isomorphism `h` of
  spaces. A `StrictBasis.Iso S S'` (an order isomorphism `σ : P ≃o P'` and an isomorphism
  `h : X ≅ X'` carrying `ι` to `ι'` and `U' (σ p)` back to `U p`) gives `Iso.BIso`
  (`S.B ≅ h_* ⋙ S'.B ⋙ σ^*`), `Iso.QIso` (`S.Q ⋙ h_* ≅ (σ⁻¹)^* ⋙ S'.Q`), `Iso.strict_iff` and
  `Iso.ephemeral_iff`.
-/

set_option autoImplicit false

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace Topology TopCat

namespace TDA.Sheaf

/-! ## Pushforward along an isomorphism of spaces -/

section Pushforward

variable (C : Type u) [Category.{v} C] {X Y : TopCat.{w}}

/-- Preimages under an isomorphism and its inverse cancel. -/
private theorem map_hom_map_inv (h : X ≅ Y) (V : Opens X) :
    (Opens.map h.hom).obj ((Opens.map h.inv).obj V) = V := by
  ext x
  change h.inv (h.hom x) ∈ V ↔ x ∈ V
  rw [TopCat.hom_inv_id_apply]

/-- Pushforward of sheaves along an isomorphism `h : X ≅ Y`, with inverse the pushforward along
`h.inv`; the unit and counit are restrictions along the equalities of preimages. -/
noncomputable def sheafPushforwardEquivalence (h : X ≅ Y) : X.Sheaf C ≌ Y.Sheaf C :=
  CategoryTheory.Equivalence.mk (TopCat.Sheaf.pushforward C h.hom)
    (TopCat.Sheaf.pushforward C h.inv)
    (NatIso.ofComponents
      (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents
        (fun V => TDA.Sheaf.restrictIso F.presheaf (map_hom_map_inv h V.unop).symm)
        (fun _ => by
          change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
          exact presheaf_map_comp_map_eq _ _ _ _ _)))
      (fun φ => by
        apply CategoryTheory.Sheaf.hom_ext
        ext V
        exact (φ.hom.naturality _).symm))
    (NatIso.ofComponents
      (fun F => ObjectProperty.isoMk _ (NatIso.ofComponents
        (fun V => TDA.Sheaf.restrictIso F.presheaf (map_hom_map_inv h.symm V.unop))
        (fun _ => by
          change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
          exact presheaf_map_comp_map_eq _ _ _ _ _)))
      (fun φ => by
        apply CategoryTheory.Sheaf.hom_ext
        ext V
        exact (φ.hom.naturality _).symm))

@[simp]
theorem sheafPushforwardEquivalence_functor (h : X ≅ Y) :
    (sheafPushforwardEquivalence C h).functor = TopCat.Sheaf.pushforward C h.hom :=
  rfl

@[simp]
theorem sheafPushforwardEquivalence_inverse (h : X ≅ Y) :
    (sheafPushforwardEquivalence C h).inverse = TopCat.Sheaf.pushforward C h.inv :=
  rfl

end Pushforward

namespace StrictBasis

noncomputable section

variable {P : Type} [SemilatticeSup P] {X : TopCat.{0}} (S : StrictBasis P X)

/-! ## The adjunction `Q ⊣ B` -/

section Adjunction

variable (C : Type u) [Category.{0} C] [HasLimits C]

/-- The right triangle at `F`: `η_{B F}` followed by `B(ε_F)` is the identity. -/
private theorem unit_app_B_comp (F : X.Sheaf C) :
    (S.unit C).app ((S.B C).obj F) ≫ (S.B C).map ((S.counitIso C).hom.app F) = 𝟙 _ := by
  have h : (S.unit C).app ((S.B C).obj F) = (S.B C).map ((S.counitIso C).inv.app F) := by
    ext t
    exact S.proj_ext _ fun s hs =>
      (S.unit_app_app_proj _ hs).trans (S.counitIso_inv_app_hom_app_proj F hs).symm
  rw [h, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (S.B C).map_id F

/-- The left triangle at `M`: `Q(η_M)` followed by `ε_{Q M}` is the identity. -/
private theorem Q_map_unit_comp (M : P ⥤ C) :
    (S.Q C).map ((S.unit C).app M) ≫ (S.counitIso C).hom.app ((S.Q C).obj M) = 𝟙 _ := by
  have h : (S.Q C).map ((S.unit C).app M) = (S.counitIso C).inv.app ((S.Q C).obj M) := by
    apply (S.B C).map_injective
    ext t
    refine S.proj_ext _ fun s hs => ?_
    refine (S.map_app_proj ((S.unit C).app M) hs).trans
      (Eq.trans ?_ (S.counitIso_inv_app_hom_app_proj ((S.Q C).obj M) hs).symm)
    refine S.proj_ext M fun s' hs' => ?_
    refine ((Category.assoc _ _ _).trans
      ((congrArg (S.proj M hs ≫ ·) (S.unit_app_app_proj M hs')).trans
        (S.proj_comp_map M hs _))).trans ?_
    exact (S.map_proj M (homOfLE (le_of_strict hs)) hs').symm
  rw [h]
  exact Iso.inv_hom_id_app _ _

/-- The adjunction `Q ⊣ B`, with unit `S.unit` and counit `S.counitIso.hom`. -/
def adjunction : S.Q C ⊣ S.B C :=
  Adjunction.mkOfUnitCounit
    { unit := S.unit C
      counit := (S.counitIso C).hom
      left_triangle := by
        refine NatTrans.ext (funext fun M => ?_)
        simpa using S.Q_map_unit_comp C M
      right_triangle := by
        refine NatTrans.ext (funext fun F => ?_)
        simpa using S.unit_app_B_comp C F }

@[simp]
theorem adjunction_unit : (S.adjunction C).unit = S.unit C :=
  rfl

@[simp]
theorem adjunction_counit : (S.adjunction C).counit = (S.counitIso C).hom :=
  rfl

variable {C}

/-- A map `Q M ⟶ F` corresponds to `η_M` followed by its image under `B`. -/
theorem adjunction_homEquiv_apply (M : P ⥤ C) (F : X.Sheaf C) (φ : (S.Q C).obj M ⟶ F) :
    (S.adjunction C).homEquiv M F φ = (S.unit C).app M ≫ (S.B C).map φ :=
  Adjunction.homEquiv_unit _ _ _ _

/-- A map `M ⟶ B F` corresponds to its image under `Q` followed by the counit. -/
theorem adjunction_homEquiv_symm_apply (M : P ⥤ C) (F : X.Sheaf C) (ψ : M ⟶ (S.B C).obj F) :
    ((S.adjunction C).homEquiv M F).symm ψ = (S.Q C).map ψ ≫ (S.counitIso C).hom.app F :=
  Adjunction.homEquiv_counit _ _ _ _

variable (C)

/-- `B` is fully faithful: the counit of `Q ⊣ B` is an isomorphism. -/
def BFullyFaithful : (S.B C).FullyFaithful :=
  haveI : IsIso (S.adjunction C).counit := (inferInstance : IsIso (S.counitIso C).hom)
  (S.adjunction C).fullyFaithfulROfIsIsoCounit

/-- `B` is full. -/
instance B_full : (S.B C).Full :=
  (S.BFullyFaithful C).full

/-- `Q` is a localization functor at the morphisms that it inverts. -/
instance Q_isLocalization :
    (S.Q C).IsLocalization ((MorphismProperty.isomorphisms _).inverseImage (S.Q C)) :=
  (S.adjunction C).isLocalization

/-- `Q` preserves limits: pushforward of sheaves is computed on presheaves, and the Alexandrov
sheaf functor is an equivalence. -/
instance Q_preservesLimits : PreservesLimits (S.Q C) := by
  have : PreservesLimits (TopCat.Presheaf.pushforward C S.ι) :=
    inferInstanceAs (PreservesLimits ((Functor.whiskeringLeft _ _ C).obj (Opens.map S.ι).op))
  have : PreservesLimits (TopCat.Sheaf.pushforward C S.ι ⋙ TopCat.Sheaf.forget C X) :=
    inferInstanceAs
      (PreservesLimits (TopCat.Sheaf.forget C _ ⋙ TopCat.Presheaf.pushforward C S.ι))
  have : PreservesLimits (TopCat.Sheaf.pushforward C S.ι) :=
    preservesLimits_of_reflects_of_preserves _ (TopCat.Sheaf.forget C X)
  unfold StrictBasis.Q
  infer_instance

/-- `Q` preserves colimits, as the left adjoint of `B`. -/
instance Q_preservesColimits : PreservesColimits (S.Q C) :=
  (S.adjunction C).leftAdjoint_preservesColimits

example : PreservesFiniteLimits (S.Q C) := inferInstance
example : PreservesFiniteColimits (S.Q C) := inferInstance

end Adjunction

/-! ## Ephemeral diagrams -/

section Ephemeral

variable (C : Type u) [Category.{0} C]

/-- The ephemeral diagrams: every map `M(s ≤ t)` with `t` strictly above `s` is zero. -/
def ephemeral [HasZeroMorphisms C] : ObjectProperty (P ⥤ C) :=
  fun M => ∀ (s t : P) (h : S.Strict s t), M.map (homOfLE (le_of_strict h)) = 0

variable {C} [HasZeroMorphisms C] [HasLimits C]

/-- A sheaf on `X` is zero exactly when its values on basic opens are. -/
theorem isZero_B_iff (F : X.Sheaf C) : IsZero ((S.B C).obj F) ↔ IsZero F := by
  refine ⟨IsZero.of_full_of_faithful_of_isZero (S.B C) F, fun h => ?_⟩
  have : PreservesLimits (S.B C) := (S.adjunction C).rightAdjoint_preservesLimits
  exact (IsZero.iff_id_eq_zero _).2 ((h.isTerminal.isTerminalObj (S.B C) F).hom_ext _ _)

/-- `Q M` is zero exactly when `M` is ephemeral: a projection at `s` factors through a map
`M(m ≤ s)` with `m` strictly between. -/
theorem ephemeral_iff (M : P ⥤ C) : S.ephemeral C M ↔ IsZero ((S.Q C).obj M) := by
  rw [← S.isZero_B_iff]
  constructor
  · intro h
    refine Functor.isZero _ fun t => (IsZero.iff_id_eq_zero _).2 ?_
    refine S.proj_ext M fun s hs => ?_
    obtain ⟨m, htm, hms⟩ := exists_strict_strict hs
    rw [Category.id_comp, zero_comp, ← S.proj_comp_map M htm (homOfLE (le_of_strict hms)),
      h _ _ hms, comp_zero]
  · intro hz s t h
    rw [← S.unit_app_app_proj M h, hz.eq_of_tgt ((S.unit C).app M) 0]
    exact zero_comp

/-- The ephemeral diagrams are the kernel of `Q`. -/
theorem ephemeral_eq_kernel : S.ephemeral C = (S.Q C).kernel := by
  funext M
  exact propext (S.ephemeral_iff M)

end Ephemeral

/-! ## The Serre localization -/

section Serre

variable (C : Type u) [Category.{0} C] [Abelian C] [HasLimits C]

/-- The category of sheaves on `X` is abelian, transported along `Q ⊣ B` with `QB ≅ 𝟭`
(`abelianOfAdjunction`). -/
@[instance_reducible]
def sheafAbelian : Abelian (X.Sheaf C) :=
  letI : Preadditive (X.Sheaf C) :=
    inferInstanceAs (Preadditive (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C))
  letI : (S.Q C).IsLeftAdjoint := (S.adjunction C).isLeftAdjoint
  abelianOfAdjunction (S.B C) (S.Q C) (S.counitIso C) (S.adjunction C)

/-- The ephemeral diagrams form a Serre class. -/
instance ephemeral_isSerreClass : (S.ephemeral C).IsSerreClass := by
  let _ := S.sheafAbelian C
  rw [ephemeral_eq_kernel]
  infer_instance

/-- The morphisms inverted by `Q` are the isomorphisms modulo ephemeral diagrams. -/
theorem ephemeral_isoModSerre :
    (S.ephemeral C).isoModSerre = (MorphismProperty.isomorphisms _).inverseImage (S.Q C) := by
  let _ := S.sheafAbelian C
  have key : ∀ (K : ObjectProperty (P ⥤ C)) [K.IsSerreClass], K = (S.Q C).kernel →
      K.isoModSerre = (MorphismProperty.isomorphisms _).inverseImage (S.Q C) := by
    rintro K _ rfl
    exact Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms (S.Q C)
  exact key _ S.ephemeral_eq_kernel

variable {C}

/-- `Q` inverts `f` exactly when the kernel and the cokernel of `f` are ephemeral. -/
theorem isIso_Q_map_iff {M N : P ⥤ C} (f : M ⟶ N) :
    IsIso ((S.Q C).map f) ↔ S.ephemeral C (kernel f) ∧ S.ephemeral C (cokernel f) := by
  have h := congrArg (fun W : MorphismProperty (P ⥤ C) => W f) (S.ephemeral_isoModSerre C)
  exact (iff_of_eq h).symm

variable (C)

/-- `Q` is a localization functor at the isomorphisms modulo ephemeral diagrams. -/
instance Q_isLocalization_isoModSerre : (S.Q C).IsLocalization (S.ephemeral C).isoModSerre :=
  (S.ephemeral_isoModSerre C) ▸ S.Q_isLocalization C

/-- The comparison of Mathlib's localization at the isomorphisms modulo ephemeral diagrams with
sheaves on `X`. -/
def localizationEquivalence : (S.ephemeral C).isoModSerre.Localization ≌ X.Sheaf C :=
  Localization.uniq (S.ephemeral C).isoModSerre.Q (S.Q C) (S.ephemeral C).isoModSerre

/-- The comparison is compatible with the localization functor and `Q`. -/
def localizationEquivalenceCompIso :
    (S.ephemeral C).isoModSerre.Q ⋙ (S.localizationEquivalence C).functor ≅ S.Q C :=
  Localization.compUniqFunctor _ _ _

end Serre

/-! ## The identity case: a reflexive strict order -/

section Identity

variable {C : Type u} [Category.{0} C]

/-- When `t` is strictly above itself, the unit at `t` is an isomorphism, with inverse the
projection to `M(t)`. -/
theorem isIso_unit_app_app_of_strict_refl [HasLimits C] (hS : ∀ t : P, S.Strict t t)
    (M : P ⥤ C) (t : P) : IsIso (((S.unit C).app M).app t) := by
  refine ⟨S.proj M (hS t), ?_, ?_⟩
  · refine (S.unit_app_app_proj M (hS t)).trans ?_
    exact (congrArg M.map (Subsingleton.elim _ (𝟙 t))).trans (M.map_id t)
  · refine S.proj_ext M fun s hs => ?_
    rw [Category.assoc, unit_app_app_proj, proj_comp_map, Category.id_comp]

/-- When the strict order is reflexive, `Q` is an equivalence: the unit and the counit of
`Q ⊣ B` are isomorphisms. -/
theorem Q_isEquivalence_of_strict_refl [HasLimits C] (hS : ∀ t : P, S.Strict t t) :
    (S.Q C).IsEquivalence := by
  have : ∀ M, IsIso ((S.adjunction C).unit.app M) := fun M =>
    haveI : ∀ t, IsIso (((S.unit C).app M).app t) := S.isIso_unit_app_app_of_strict_refl hS M
    NatIso.isIso_of_isIso_app ((S.unit C).app M)
  have : ∀ F, IsIso ((S.adjunction C).counit.app F) := fun F =>
    (inferInstance : IsIso ((S.counitIso C).hom.app F))
  exact ((S.adjunction C).toEquivalence).isEquivalence_functor

/-- When the strict order is reflexive, the ephemeral diagrams are the zero diagrams. -/
theorem ephemeral_iff_isZero_of_strict_refl [HasZeroMorphisms C] (hS : ∀ t : P, S.Strict t t)
    (M : P ⥤ C) : S.ephemeral C M ↔ IsZero M := by
  refine ⟨fun h => Functor.isZero _ fun t => (IsZero.iff_id_eq_zero _).2 ?_,
    fun h s _ _ => ?_⟩
  · rw [← M.map_id t, ← h t t (hS t)]
    exact congrArg M.map (Subsingleton.elim _ _)
  · have h0 : 𝟙 (M.obj s) = 0 :=
      congrArg (fun f => NatTrans.app f s) ((IsZero.iff_id_eq_zero M).1 h)
    rw [← Category.id_comp (M.map _), h0, zero_comp]

end Identity

/-! ## Comparison along isomorphisms -/

/-- An isomorphism of strict bases: an order isomorphism of the index sets and an isomorphism
of the spaces, compatible with the maps `ι` and the basic opens. -/
structure Iso {P' : Type} [SemilatticeSup P'] {X' : TopCat.{0}} (S' : StrictBasis P' X') where
  /-- The order isomorphism of the index sets. -/
  orderIso : P ≃o P'
  /-- The isomorphism of the spaces. -/
  homeo : X ≅ X'
  /-- The isomorphism carries `ι` to `ι'`. -/
  hom_ι (p : P) : homeo.hom (S.ι (WithUpperSet.toUpperSet p)) =
    S'.ι (WithUpperSet.toUpperSet (orderIso p))
  /-- The basic open at `orderIso p` pulls back to the basic open at `p`. -/
  map_U (p : P) : (Opens.map homeo.hom).obj (S'.U (orderIso p)) = S.U p

namespace Iso

variable {S} {P' : Type} [SemilatticeSup P'] {X' : TopCat.{0}} {S' : StrictBasis P' X'}
  (e : S.Iso S')

/-- An isomorphism of strict bases preserves the strict order. -/
theorem strict_iff {s t : P} : S'.Strict (e.orderIso s) (e.orderIso t) ↔ S.Strict s t := by
  change S'.ι (WithUpperSet.toUpperSet (e.orderIso t)) ∈ S'.U (e.orderIso s) ↔
    S.ι (WithUpperSet.toUpperSet t) ∈ S.U s
  rw [← e.hom_ι, ← e.map_U s]
  rfl

variable (C : Type u) [Category.{0} C]

/-- `B` commutes with the comparison: `B F` is `B'` of the pushforward of `F`, reindexed along
the order isomorphism. -/
def BIso : S.B C ≅ (sheafPushforwardEquivalence C e.homeo).functor ⋙ S'.B C ⋙
    (Functor.whiskeringLeft P P' C).obj e.orderIso.monotone.functor :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun p => TDA.Sheaf.restrictIso F.presheaf (e.map_U p).symm)
      (fun _ => presheaf_map_comp_map_eq _ _ _ _ _))
    (fun φ => by
      apply NatTrans.ext
      funext p
      exact (φ.hom.naturality _).symm)

@[simp]
theorem BIso_hom_app_app (F : X.Sheaf C) (p : P) :
    ((e.BIso C).hom.app F).app p = F.presheaf.map (homOfLE (e.map_U p).le).op :=
  rfl

variable [HasLimits C]

/-- The left adjoint of `B'` transported along the comparison. -/
private def transportedAdjunction :
    ((e.orderIso.equivalence.congrLeft (E := C)).functor ⋙ S'.Q C ⋙
        (sheafPushforwardEquivalence C e.homeo).inverse) ⊣ S.B C :=
  Adjunction.ofNatIsoRight
    ((e.orderIso.equivalence.congrLeft (E := C)).toAdjunction.comp
      ((S'.adjunction C).comp (sheafPushforwardEquivalence C e.homeo).symm.toAdjunction))
    (e.BIso C).symm

/-- `Q` commutes with the comparison: pushing `Q M` forward is `Q'` of `M` reindexed along the
inverse order isomorphism. By uniqueness of left adjoints of `B`. -/
def QIso : S.Q C ⋙ (sheafPushforwardEquivalence C e.homeo).functor ≅
    (Functor.whiskeringLeft P' P C).obj e.orderIso.symm.monotone.functor ⋙ S'.Q C :=
  Functor.isoWhiskerRight ((S.adjunction C).leftAdjointUniq (e.transportedAdjunction C))
      (sheafPushforwardEquivalence C e.homeo).functor ≪≫
    Functor.isoWhiskerLeft ((e.orderIso.equivalence.congrLeft (E := C)).functor ⋙ S'.Q C)
      (sheafPushforwardEquivalence C e.homeo).counitIso ≪≫ Functor.rightUnitor _

end Iso

variable {S} in
/-- A diagram on `P'` is ephemeral for `S'` exactly when its reindexing along the order
isomorphism is ephemeral for `S`. -/
theorem Iso.ephemeral_iff {P' : Type} [SemilatticeSup P'] {X' : TopCat.{0}}
    {S' : StrictBasis P' X'} (e : S.Iso S') {C : Type u} [Category.{0} C] [HasZeroMorphisms C]
    (M : P' ⥤ C) :
    S.ephemeral C (e.orderIso.monotone.functor ⋙ M) ↔ S'.ephemeral C M := by
  constructor
  · intro h s' t' hst
    obtain ⟨s, rfl⟩ := e.orderIso.surjective s'
    obtain ⟨t, rfl⟩ := e.orderIso.surjective t'
    exact h s t (e.strict_iff.1 hst)
  · intro h s t hst
    exact h _ _ (e.strict_iff.2 hst)

end

end StrictBasis

end TDA.Sheaf
