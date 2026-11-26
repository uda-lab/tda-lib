import TDA.Sheaf.RealConstructible
import TDA.Sheaf.AlternatingHeredity
import TDA.Sheaf.IntervalCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The extension–sections adjunction on all sheaves of the real line

Fix strictly increasing breakpoints `p : Fin m → ℝ` (`hp : StrictMono p`) and write `Φ` for
`extension k hp` and `Γ` for `sections k p` (`TDA.Sheaf.RealConstructible`).

* `starTauAdjunction`: the stars `v ↦ star p v` (`starBasic`) are left adjoint to the stratum
  functor `tauFunctor hp`, between the free category of the strata and the opposite category of
  basic opens. Both categories are thin; the unit is `tau_star` and the counit is
  `le_star_tau`.
* `extensionAdjunction : Φ ⊣ Γ` for **every** sheaf of `k`-modules on `ℝ`: precomposition with
  `tauFunctor hp` is left adjoint to precomposition with the stars (`Adjunction.whiskerLeft`),
  and `basisEquiv` transports this to sheaves on `ℝ`. Its unit is the inverse of D1's counit
  `extensionSectionsIso` (`extensionAdjunction_unit`), and on constructible sheaves its counit
  is the inverse of D1's unit `sectionsExtensionIso` (`extensionAdjunction_counit_app`). The
  equivalence `equivalence k hp` of D1 is therefore the restriction of this adjunction
  (`equivalence_counitIso_inv_app_hom`, `equivalence_unitIso_inv_app_hom`).
* `Φ` is fully faithful (`extensionFullyFaithful`), additive, and preserves finite limits and
  finite colimits.
* The universal property of `Φ P_v` on the open star `star p v`: for every sheaf `F`,
  `Hom(Φ P_v, F) ≃ F(star p v)` (`homExtensionRepresentableEquiv`, evaluation at the generator
  `starGenerator`, natural in `F`), and `Hom(Φ (P_v ⊗ V), F) ≃ Hom_k(V, F(star p v))`
  (`homExtensionPathTensorEquiv`).
* `HasExt.{0}` holds for sheaves of `k`-modules on `ℝ` (`hasExt_sheaf_realLine`) and for the
  diagrams (`hasExt_diagram`).
* `Ext` out of `Φ` of projectives through an injective resolution `R` of a sheaf `Y`:
  `ext_extension_eq_zero_of_lift` reduces the vanishing of `Ext^{q+1}(Φ M, Y)` to a lifting
  problem for `Hom(M, Γ R)`; `ext_extension_representable_eq_zero` (for `P_v`) and
  `ext_extension_sumTensor_eq_zero` (for the sums `⊕_j P_(σ j) ⊗ V_j` of D2's resolution) read
  it off exactness of the sections of `R` over the stars.
* `extStarEquiv`: `Ext^{q+1}(Φ P_v, Y)` is the cohomology in degree `q + 1` of the complex of
  sections of `R` over `star p v`: cocycles (`starCocycles`) modulo coboundaries
  (`starCoboundaries`). The map from cocycles is `extOfStarCocycle`, built with Mathlib's
  `InjectiveResolution.extMk`.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace Opposite Abelian TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification

namespace TDA.Sheaf.RealConstructible

variable {m : ℕ} {p : Fin m → ℝ}

/-! ### Stars and strata -/

/-- The stars as a functor into the opposite category of basic opens: `starFunctor` factored
through the basis. -/
noncomputable def starBasic (hp : StrictMono p) :
    Paths (Vertex (orient m)) ⥤ (BasicCat (breakpoints p))ᵒᵖ :=
  Paths.lift
    { obj := fun v => op (⟨star p v, isBasicOpen_star hp v⟩ : Basic (breakpoints p))
      map := fun {v w} e => Quiver.Hom.op (InducedCategory.homMk
        (X := (⟨star p w, isBasicOpen_star hp w⟩ : Basic (breakpoints p)))
        (Y := (⟨star p v, isBasicOpen_star hp v⟩ : Basic (breakpoints p)))
        (homOfLE (star_le_star_of_arrow p e.down))) }

/-- **The stars are left adjoint to the strata.** Both categories are thin; the unit is the
identity `v = tau (star v)` and the counit is the inclusion of a basic open into the star of
its stratum. -/
noncomputable def starTauAdjunction (hp : StrictMono p) : starBasic hp ⊣ tauFunctor hp :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun v => eqToHom (congrArg (vtx (orient m))
            (tau_star hp v (isBasicOpen_star hp v)).symm)
          naturality := fun _ _ _ => Subsingleton.elim _ _ }
      counit :=
        { app := fun U => Quiver.Hom.op (InducedCategory.homMk (homOfLE (le_star_tau hp U.unop)))
          naturality := by
            intros
            exact Quiver.Hom.unop_inj (Subsingleton.elim _ _) }
      left_triangle := by
        ext v
        exact Subsingleton.elim _ _
      right_triangle := by
        ext U
        exact Subsingleton.elim _ _ }

variable (k : Type) [Field k]

/-- Precomposition with `tauFunctor` is left adjoint to precomposition with the stars. -/
private noncomputable def precompAdjunction (hp : StrictMono p) :
    (Functor.whiskeringLeft _ _ (ModuleCat.{0} k)).obj (tauFunctor hp) ⊣
      (Functor.whiskeringLeft _ _ (ModuleCat.{0} k)).obj (starBasic hp) :=
  (starTauAdjunction hp).whiskerLeft (ModuleCat.{0} k)

/-- `basisSheaf ⊣ (restriction to the stars)` on sheaves on the basis. -/
private noncomputable def basisSheafAdjunction (hp : StrictMono p) :
    basisSheaf k hp ⊣ (sheafToPresheaf (basicTopology (breakpoints p)) (ModuleCat.{0} k) ⋙
      (Functor.whiskeringLeft _ _ (ModuleCat.{0} k)).obj (starBasic hp)) :=
  Adjunction.mkOfUnitCounit
    { unit := (precompAdjunction k hp).unit
      counit :=
        { app := fun P => ObjectProperty.homMk ((precompAdjunction k hp).counit.app P.obj)
          naturality := fun _ _ f => ObjectProperty.hom_ext _
            ((precompAdjunction k hp).counit.naturality f.hom) }
      left_triangle := by
        ext M : 2
        exact ObjectProperty.hom_ext _ ((precompAdjunction k hp).left_triangle_components M)
      right_triangle := by
        ext P : 2
        exact (precompAdjunction k hp).right_triangle_components P.obj }

/-- The right adjoint obtained on the basis is `Γ`: componentwise this is the identity
`F(star v) = F(star v)`. -/
private noncomputable def rightAdjointIsoSections (hp : StrictMono p) :
    ((basisEquiv (breakpoints p) k).inverse ⋙
      (sheafToPresheaf (basicTopology (breakpoints p)) (ModuleCat.{0} k) ⋙
        (Functor.whiskeringLeft _ _ (ModuleCat.{0} k)).obj (starBasic hp))) ≅ sections k p :=
  NatIso.ofComponents
    (fun F => isoMk (fun _ => Iso.refl _) (by
      intro v w h
      exact congrArg F.obj.map (Subsingleton.elim _ _)))
    (fun _ => by
      apply NatTrans.ext
      funext _
      rfl)

/-- **`Φ ⊣ Γ` on all sheaves of `k`-modules on `ℝ`**, not only constructible ones: the
adjunction `basisSheaf ⊣ (restriction to the stars)` on the basis, transported along
`basisEquiv`. -/
noncomputable def extensionAdjunction (hp : StrictMono p) : extension k hp ⊣ sections k p :=
  ((basisSheafAdjunction k hp).comp (basisEquiv (breakpoints p) k).toAdjunction).ofNatIsoRight
    (rightAdjointIsoSections k hp)

/-- **The unit of `Φ ⊣ Γ` is the inverse of D1's counit** `extensionSectionsIso`. -/
theorem extensionAdjunction_unit (hp : StrictMono p) :
    (extensionAdjunction k hp).unit = (extensionSectionsIso k hp).inv := by
  ext M : 2
  apply NatTrans.ext
  funext v
  have h1 : ((extensionAdjunction k hp).unit.app M).app v =
      M.map ((starTauAdjunction hp).unit.app v) ≫
        ((basisEquiv (breakpoints p) k).unitIso.hom.app ((basisSheaf k hp).obj M)).hom.app
          ((starBasic hp).obj v) := by
    simp [extensionAdjunction, Adjunction.ofNatIsoRight, Adjunction.comp_unit_app,
      basisSheafAdjunction, precompAdjunction, rightAdjointIsoSections]
    exact congrArg (_ ≫ ·) (Category.comp_id _)
  have h2 : ((extensionSectionsIso k hp).inv.app M).app v =
      M.map (eqToHom (congrArg (vtx (orient m)) (tau_star hp v (isBasicOpen_star hp v))).symm) ≫
        ((basisEquiv (breakpoints p) k).unitIso.hom.app ((basisSheaf k hp).obj M)).hom.app
          ((starBasic hp).obj v) := rfl
  rw [h1, h2]
  exact congrArg (· ≫ _) (congrArg M.map (Subsingleton.elim _ _))

/-- The components of `toBasis`: restriction from the star of the stratum. -/
theorem toBasis_app_hom_app (hp : StrictMono p) (F : TopCat.Sheaf (ModuleCat.{0} k) realLine)
    (U : (BasicCat (breakpoints p))ᵒᵖ) :
    ((toBasis k hp).app F).hom.app U = F.presheaf.map (homOfLE (le_star_tau hp U.unop)).op :=
  rfl

/-- The counit of `Φ ⊣ Γ` on every sheaf: `basisEquiv` applied to the restrictions from the
stars of the strata (`toBasis`), followed by the counit of `basisEquiv`. -/
theorem extensionAdjunction_counit_app_eq (hp : StrictMono p)
    (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) :
    (extensionAdjunction k hp).counit.app F =
      (basisEquiv (breakpoints p) k).functor.map ((toBasis k hp).app F) ≫
        (basisEquiv (breakpoints p) k).counitIso.hom.app F := by
  have h' : (basisSheaf k hp).map ((rightAdjointIsoSections k hp).inv.app F) ≫
      (basisSheafAdjunction k hp).counit.app ((basisEquiv (breakpoints p) k).inverse.obj F) =
        (toBasis k hp).app F := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    simp [basisSheafAdjunction, precompAdjunction, starTauAdjunction, toBasis_app_hom_app,
      rightAdjointIsoSections, basisSheaf]
    exact Category.id_comp _
  rw [← h', Functor.map_comp, Category.assoc]
  simp only [extensionAdjunction, Adjunction.ofNatIsoRight]
  rfl

/-- **On constructible sheaves, the counit of `Φ ⊣ Γ` is the inverse of D1's unit**
`sectionsExtensionIso`. -/
theorem extensionAdjunction_counit_app (hp : StrictMono p) (F : Constructible k p) :
    (extensionAdjunction k hp).counit.app F.obj = (sectionsExtensionIso k hp).inv.app F := by
  rw [extensionAdjunction_counit_app_eq]
  rfl

/-- **D1's equivalence is the restriction of `Φ ⊣ Γ`: the unit.** The inverse of the counit of
`equivalence k hp` at a finite diagram `M` is the unit of `extensionAdjunction` at `M`. -/
theorem equivalence_counitIso_inv_app_hom (hp : StrictMono p) (M : FinDiagram k m) :
    ((equivalence k hp).counitIso.inv.app M).hom = (extensionAdjunction k hp).unit.app M.obj := by
  rw [extensionAdjunction_unit]
  exact congrArg (fun φ => NatTrans.app φ M)
    (((ObjectProperty.fullyFaithfulι _).whiskeringRight (FinDiagram k m)).map_preimage
      (X := 𝟭 _) (Y := extensionFin k hp ⋙ sectionsFin k hp)
      (Functor.isoWhiskerLeft (ObjectProperty.ι _) (extensionSectionsIso k hp)).inv)

/-- **D1's equivalence is the restriction of `Φ ⊣ Γ`: the counit.** The inverse of the unit of
`equivalence k hp` at a constructible sheaf `F` is the counit of `extensionAdjunction` at `F`. -/
theorem equivalence_unitIso_inv_app_hom (hp : StrictMono p) (F : Constructible k p) :
    ((equivalence k hp).unitIso.inv.app F).hom = (extensionAdjunction k hp).counit.app F.obj := by
  let B := extensionAdjunction k hp
  let A := (equivalence k hp).symm.toAdjunction
  let x : (extension k hp).obj ((sections k p).obj F.obj) ⟶ F.obj :=
    ((equivalence k hp).unitIso.inv.app F).hom
  have key : B.unit.app ((sections k p).obj F.obj) ≫ (sections k p).map x = 𝟙 _ :=
    (congrArg (· ≫ (sections k p).map x)
      (equivalence_counitIso_inv_app_hom k hp ((sectionsFin k hp).obj F)).symm).trans
      (congrArg (fun f => f.hom) (A.right_triangle_components F))
  change x = _
  calc x = (B.homEquiv _ _).symm (B.homEquiv _ _ x) := (Equiv.symm_apply_apply _ _).symm
    _ = (extension k hp).map (B.unit.app _ ≫ (sections k p).map x) ≫ B.counit.app F.obj := by
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
    _ = B.counit.app F.obj := by rw [key, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **`Φ` is fully faithful**: the unit of `Φ ⊣ Γ` is invertible (D1's `extensionSectionsIso`). -/
noncomputable def extensionFullyFaithful (hp : StrictMono p) : (extension k hp).FullyFaithful :=
  (extensionAdjunction k hp).fullyFaithfulLOfCompIsoId (extensionSectionsIso k hp)

instance extension_full (hp : StrictMono p) : (extension k hp).Full :=
  (extensionFullyFaithful k hp).full

instance extension_faithful (hp : StrictMono p) : (extension k hp).Faithful :=
  (extensionFullyFaithful k hp).faithful

/-- `Φ` preserves finite colimits (it is a left adjoint). -/
instance preservesFiniteColimits_extension (hp : StrictMono p) :
    PreservesFiniteColimits (extension k hp) :=
  haveI := (extensionAdjunction k hp).isLeftAdjoint
  inferInstance

/-- `Φ` preserves finite limits: precomposition with `tauFunctor` preserves limits, sheaves on
the basis are closed under limits, and `basisEquiv` is an equivalence. -/
instance preservesFiniteLimits_extension (hp : StrictMono p) :
    PreservesFiniteLimits (extension k hp) := by
  have : PreservesFiniteLimits (basisSheaf k hp ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ (ModuleCat.{0} k)).obj (tauFunctor hp)))
  have : PreservesFiniteLimits (basisSheaf k hp) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have : PreservesFiniteLimits (basisEquiv (breakpoints p) k).functor := by
    have : PreservesLimitsOfSize.{0, 0} (basisEquiv (breakpoints p) k).functor :=
      (basisEquiv (breakpoints p) k).symm.toAdjunction.rightAdjoint_preservesLimits
    infer_instance
  change PreservesFiniteLimits (basisSheaf k hp ⋙ (basisEquiv (breakpoints p) k).functor)
  infer_instance

/-- `Γ` is additive: sections are computed objectwise. -/
instance sections_additive (p : Fin m → ℝ) : (sections k p).Additive where
  map_add := rfl

/-- `Φ` is additive (a left adjoint of the additive `Γ`). -/
instance extension_additive (hp : StrictMono p) : (extension k hp).Additive :=
  (extensionAdjunction k hp).left_adjoint_additive

/-! ### The universal property of `Φ P_v` on the open star -/

/-- The generator of `Φ P_v` over the star of `v`: the image of `1` in the slot of the
identity path of `P_v`, read in `(Φ P_v)(star p v)` through `extensionStarIso`. -/
noncomputable def starGenerator (hp : StrictMono p) (v : Fin (2 * m + 1)) :
    ((extension k hp).obj (representable k (orient m) v)).presheaf.obj (op (star p v)) :=
  (extensionStarIso k hp (representable k (orient m) v) v).inv.hom
    ((pathSlot v (ModuleCat.of k k) (𝟙 _)).hom 1)

/-- **The universal property of `Φ P_v`.** For every sheaf `F` of `k`-modules on `ℝ`,
morphisms `Φ P_v ⟶ F` are the sections of `F` over the open star `star p v`. -/
noncomputable def homExtensionRepresentableEquiv (hp : StrictMono p) (v : Fin (2 * m + 1))
    (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) :
    ((extension k hp).obj (representable k (orient m) v) ⟶ F) ≃
      F.presheaf.obj (op (star p v)) :=
  ((extensionAdjunction k hp).homEquiv _ _).trans
    (representableHomEquiv v ((sections k p).obj F))

/-- The universal property evaluates a morphism at the generator `starGenerator`. -/
theorem homExtensionRepresentableEquiv_apply (hp : StrictMono p) (v : Fin (2 * m + 1))
    (F : TopCat.Sheaf (ModuleCat.{0} k) realLine)
    (f : (extension k hp).obj (representable k (orient m) v) ⟶ F) :
    homExtensionRepresentableEquiv k hp v F f = f.hom.app _ (starGenerator k hp v) := by
  change representableHomEquiv v ((sections k p).obj F)
    ((extensionAdjunction k hp).homEquiv _ _ f) = _
  rw [representableHomEquiv_apply, Adjunction.homEquiv_unit, extensionAdjunction_unit]
  rfl

/-- Naturality of `homExtensionRepresentableEquiv` in the sheaf. -/
theorem homExtensionRepresentableEquiv_comp (hp : StrictMono p) (v : Fin (2 * m + 1))
    {F G : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (f : (extension k hp).obj (representable k (orient m) v) ⟶ F) (g : F ⟶ G) :
    homExtensionRepresentableEquiv k hp v G (f ≫ g) =
      g.hom.app _ (homExtensionRepresentableEquiv k hp v F f) := by
  rw [homExtensionRepresentableEquiv_apply, homExtensionRepresentableEquiv_apply]
  rfl

/-- `homExtensionRepresentableEquiv` is additive. -/
theorem homExtensionRepresentableEquiv_add (hp : StrictMono p) (v : Fin (2 * m + 1))
    (F : TopCat.Sheaf (ModuleCat.{0} k) realLine)
    (f g : (extension k hp).obj (representable k (orient m) v) ⟶ F) :
    homExtensionRepresentableEquiv k hp v F (f + g) =
      homExtensionRepresentableEquiv k hp v F f + homExtensionRepresentableEquiv k hp v F g := by
  rw [homExtensionRepresentableEquiv_apply, homExtensionRepresentableEquiv_apply,
    homExtensionRepresentableEquiv_apply]
  rfl

/-- `homExtensionRepresentableEquiv` sends `0` to `0`. -/
theorem homExtensionRepresentableEquiv_zero (hp : StrictMono p) (v : Fin (2 * m + 1))
    (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) :
    homExtensionRepresentableEquiv k hp v F 0 = 0 := by
  have h := homExtensionRepresentableEquiv_add k hp v F 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

/-- **The universal property of `Φ (P_v ⊗ V)`.** For every sheaf `F` of `k`-modules on `ℝ`,
morphisms `Φ (P_v ⊗ V) ⟶ F` are the linear maps from `V` to the sections of `F` over the open
star `star p v`. -/
noncomputable def homExtensionPathTensorEquiv (hp : StrictMono p) (v : Fin (2 * m + 1))
    (V : ModuleCat.{0} k) (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) :
    ((extension k hp).obj ((pathTensor k (orient m) v).obj V) ⟶ F) ≃
      (V ⟶ F.presheaf.obj (op (star p v))) :=
  ((extensionAdjunction k hp).homEquiv _ _).trans
    ((pathTensorAdjunction k (orient m) v).homEquiv _ _)

/-- `homExtensionPathTensorEquiv` restricts a morphism to the slot of the identity path, read
over the star through `extensionStarIso`. -/
theorem homExtensionPathTensorEquiv_apply (hp : StrictMono p) (v : Fin (2 * m + 1))
    (V : ModuleCat.{0} k) (F : TopCat.Sheaf (ModuleCat.{0} k) realLine)
    (f : (extension k hp).obj ((pathTensor k (orient m) v).obj V) ⟶ F) :
    homExtensionPathTensorEquiv k hp v V F f = pathSlot v V (𝟙 _) ≫
      (extensionStarIso k hp ((pathTensor k (orient m) v).obj V) v).inv ≫
        f.hom.app (op (star p v)) := by
  change (pathTensorAdjunction k (orient m) v).homEquiv _ _
    ((extensionAdjunction k hp).homEquiv _ _ f) = _
  rw [pathTensorAdjunction_homEquiv_apply, Adjunction.homEquiv_unit, extensionAdjunction_unit]
  rfl

/-- Naturality of `homExtensionPathTensorEquiv` in the sheaf. -/
theorem homExtensionPathTensorEquiv_comp (hp : StrictMono p) (v : Fin (2 * m + 1))
    (V : ModuleCat.{0} k) {F G : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (f : (extension k hp).obj ((pathTensor k (orient m) v).obj V) ⟶ F) (g : F ⟶ G) :
    homExtensionPathTensorEquiv k hp v V G (f ≫ g) =
      homExtensionPathTensorEquiv k hp v V F f ≫ g.hom.app (op (star p v)) := by
  rw [homExtensionPathTensorEquiv_apply, homExtensionPathTensorEquiv_apply]
  rfl

/-! ### `Ext` out of `Φ` of projectives -/

/-- Sheaves of `k`-modules on the real line have `Ext` groups in `Type`. -/
theorem hasExt_sheaf_realLine : HasExt.{0} (TopCat.Sheaf (ModuleCat.{0} k) realLine) :=
  hasExt_of_enoughInjectives _

/-- Diagrams on an oriented path have `Ext` groups in `Type`. -/
theorem hasExt_diagram {n : ℕ} (o : Fin n → Bool) : HasExt.{0} (Diagram k o) :=
  hasExt_of_enoughProjectives _

/-! ### Cocycles of sections over the star -/

/-- The cocycles of degree `n` of the complex of sections over `star p v` of an injective
resolution `R`. -/
def starCocycles (p : Fin m → ℝ) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (R : InjectiveResolution Y) (n : ℕ) :
    Submodule k ((R.cocomplex.X n).presheaf.obj (op (star p v))) :=
  LinearMap.ker ((R.cocomplex.d n (n + 1)).hom.app (op (star p v))).hom

/-- The coboundaries of degree `q + 1` of the complex of sections over `star p v` of an
injective resolution `R`. -/
def starCoboundaries (p : Fin m → ℝ) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (R : InjectiveResolution Y) (q : ℕ) :
    Submodule k ((R.cocomplex.X (q + 1)).presheaf.obj (op (star p v))) :=
  LinearMap.range ((R.cocomplex.d q (q + 1)).hom.app (op (star p v))).hom

/-- The cohomology in degree `q + 1` of the complex of sections over `star p v` of an injective
resolution `R`: cocycles modulo coboundaries. -/
abbrev starCohomology (p : Fin m → ℝ) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    (R : InjectiveResolution Y) (q : ℕ) : Type :=
  starCocycles k p v R (q + 1) ⧸
    ((starCoboundaries k p v R q).comap (starCocycles k p v R (q + 1)).subtype).toAddSubgroup

/-- The morphism `Φ P_v ⟶ R^{q+1}` of a cocycle of sections over the star is a cocycle. -/
theorem homExtensionRepresentableEquiv_symm_comp_d (hp : StrictMono p) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine} (R : InjectiveResolution Y) (q : ℕ)
    (z : starCocycles k p v R (q + 1)) :
    (homExtensionRepresentableEquiv k hp v _).symm z.1 ≫ R.cocomplex.d (q + 1) (q + 2) = 0 :=
  (homExtensionRepresentableEquiv k hp v _).injective (by
    rw [homExtensionRepresentableEquiv_comp, Equiv.apply_symm_apply,
      homExtensionRepresentableEquiv_zero]
    exact LinearMap.mem_ker.1 z.2)

section Ext

variable [HasExt.{0} (TopCat.Sheaf (ModuleCat.{0} k) realLine)]

/-- **`Ext` out of `Φ M` through an injective resolution.** Let `R` be an injective resolution
of a sheaf `Y`. If every morphism `M ⟶ Γ(R^{q+1})` killed by `Γ(d)` factors through
`Γ(d) : Γ(R^q) ⟶ Γ(R^{q+1})`, then `Ext^{q+1}(Φ M, Y) = 0`. -/
theorem ext_extension_eq_zero_of_lift (hp : StrictMono p) (M : Diagram k (orient m))
    (Y : TopCat.Sheaf (ModuleCat.{0} k) realLine) (R : InjectiveResolution Y) (q : ℕ)
    (hR : ∀ φ : M ⟶ (sections k p).obj (R.cocomplex.X (q + 1)),
      φ ≫ (sections k p).map (R.cocomplex.d (q + 1) (q + 2)) = 0 →
      ∃ ψ : M ⟶ (sections k p).obj (R.cocomplex.X q),
        ψ ≫ (sections k p).map (R.cocomplex.d q (q + 1)) = φ)
    (e : Abelian.Ext ((extension k hp).obj M) Y (q + 1)) : e = 0 := by
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective e (q + 2) rfl
  rw [R.extMk_eq_zero_iff f (q + 2) rfl hf q rfl]
  let adj := extensionAdjunction k hp
  obtain ⟨ψ, hψ⟩ := hR (adj.homEquiv _ _ f) (by
    rw [← Adjunction.homEquiv_naturality_right, hf, Adjunction.homEquiv_unit,
      Functor.map_zero, comp_zero])
  refine ⟨(adj.homEquiv _ _).symm ψ, ?_⟩
  rw [← Adjunction.homEquiv_naturality_right_symm, hψ, Equiv.symm_apply_apply]

/-- **`Ext` out of `Φ P_v` is computed by sections over the open star.** If the sections over
`star p v` of an injective resolution `R` of `Y` are exact in degree `q + 1`, then
`Ext^{q+1}(Φ P_v, Y) = 0`. -/
theorem ext_extension_representable_eq_zero (hp : StrictMono p) (v : Fin (2 * m + 1))
    (Y : TopCat.Sheaf (ModuleCat.{0} k) realLine) (R : InjectiveResolution Y) (q : ℕ)
    (hR : ∀ s : (R.cocomplex.X (q + 1)).presheaf.obj (op (star p v)),
      (R.cocomplex.d (q + 1) (q + 2)).hom.app _ s = 0 →
      ∃ t : (R.cocomplex.X q).presheaf.obj (op (star p v)),
        (R.cocomplex.d q (q + 1)).hom.app _ t = s)
    (e : Abelian.Ext ((extension k hp).obj (representable k (orient m) v)) Y (q + 1)) :
    e = 0 := by
  have hR' : ∀ s : ((sections k p).obj (R.cocomplex.X (q + 1))).obj (vtx _ v),
      (((sections k p).map (R.cocomplex.d (q + 1) (q + 2))).app _).hom s = 0 →
      ∃ t : ((sections k p).obj (R.cocomplex.X q)).obj (vtx _ v),
        (((sections k p).map (R.cocomplex.d q (q + 1))).app _).hom t = s := hR
  refine ext_extension_eq_zero_of_lift k hp _ Y R q (fun φ hφ => ?_) e
  have key : ∀ {X Z : Diagram k (orient m)} (φ : representable k (orient m) v ⟶ X) (g : X ⟶ Z),
      representableHomEquiv v Z (φ ≫ g) = (g.app (vtx _ v)).hom (representableHomEquiv v X φ) :=
    fun _ _ => rfl
  have h0 : ∀ X : Diagram k (orient m), representableHomEquiv v X 0 = 0 := fun _ => rfl
  obtain ⟨t, ht⟩ := hR' (representableHomEquiv v _ φ) (by
    have := key φ ((sections k p).map (R.cocomplex.d (q + 1) (q + 2)))
    rw [hφ, h0] at this
    exact this.symm)
  refine ⟨(representableHomEquiv v _).symm t, (representableHomEquiv v _).injective ?_⟩
  rw [key, Equiv.apply_symm_apply]
  exact ht

/-- **E3: `Ext` out of `Φ` of the sums of D2's resolution.** If the sections over each star
`star p (σ j)` of an injective resolution `R` of `Y` are exact in degree `q + 1`, then
`Ext^{q+1}(Φ (⊕_j P_(σ j) ⊗ V_j), Y) = 0`. -/
theorem ext_extension_sumTensor_eq_zero (hp : StrictMono p) {J : Type} [Fintype J]
    (σ : J → Fin (2 * m + 1)) (V : J → ModuleCat.{0} k)
    (Y : TopCat.Sheaf (ModuleCat.{0} k) realLine) (R : InjectiveResolution Y) (q : ℕ)
    (hR : ∀ j (s : (R.cocomplex.X (q + 1)).presheaf.obj (op (star p (σ j)))),
      (R.cocomplex.d (q + 1) (q + 2)).hom.app _ s = 0 →
      ∃ t : (R.cocomplex.X q).presheaf.obj (op (star p (σ j))),
        (R.cocomplex.d q (q + 1)).hom.app _ t = s)
    (e : Abelian.Ext ((extension k hp).obj (sumTensor (o := orient m) σ V)) Y (q + 1)) :
    e = 0 := by
  refine ext_extension_eq_zero_of_lift k hp _ Y R q (fun φ hφ => ?_) e
  let A := (sections k p).obj (R.cocomplex.X q)
  let B := (sections k p).obj (R.cocomplex.X (q + 1))
  let C := (sections k p).obj (R.cocomplex.X (q + 2))
  let d₀ := (sections k p).map (R.cocomplex.d q (q + 1))
  let d₁ := (sections k p).map (R.cocomplex.d (q + 1) (q + 2))
  let ιj := fun j => biproduct.ι (fun j => (pathTensor k (orient m) (σ j)).obj (V j)) j
  -- The components `a j : V j ⟶ B(σ j)` of `φ`, and their lifts `b j : V j ⟶ A(σ j)`.
  let a := fun j => (pathTensorAdjunction k (orient m) (σ j)).homEquiv _ _ (ιj j ≫ φ)
  have ha : ∀ j, a j ≫ d₁.app (vtx _ (σ j)) = 0 := fun j => by
    have := ((pathTensorAdjunction k (orient m) (σ j)).homEquiv_naturality_right (ιj j ≫ φ) d₁).symm
    rw [Category.assoc, hφ, comp_zero] at this
    refine this.trans ?_
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_zero, comp_zero]
  have hb : ∀ j, ∃ b : V j ⟶ A.obj (vtx _ (σ j)), b ≫ d₀.app (vtx _ (σ j)) = a j := by
    intro j
    let K := LinearMap.ker (d₁.app (vtx _ (σ j))).hom
    have hdd : ∀ x, (d₀.app (vtx _ (σ j))).hom x ∈ K := fun x => by
      change ((d₀ ≫ d₁).app _).hom x = 0
      rw [← Functor.map_comp, R.cocomplex.d_comp_d, Functor.map_zero]
      rfl
    let d₀' : A.obj (vtx _ (σ j)) →ₗ[k] K :=
      LinearMap.codRestrict K (d₀.app (vtx _ (σ j))).hom hdd
    let a' : V j →ₗ[k] K := LinearMap.codRestrict K (a j).hom fun x => by
      change ((a j ≫ d₁.app _)).hom x = 0
      rw [ha]
      rfl
    have hsurj : Function.Surjective d₀' := fun ⟨s, hs⟩ => by
      obtain ⟨t, ht⟩ := hR j s hs
      exact ⟨t, Subtype.ext ht⟩
    obtain ⟨h, hh⟩ := Module.projective_lifting_property d₀' a' hsurj
    refine ⟨ModuleCat.ofHom h, ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
    exact congrArg Subtype.val (LinearMap.congr_fun hh x)
  choose b hb using hb
  refine ⟨sumTensorDesc σ V A b, biproduct.hom_ext' _ _ fun j =>
    ((pathTensorAdjunction k (orient m) (σ j)).homEquiv _ _).injective ?_⟩
  change (pathTensorAdjunction k (orient m) (σ j)).homEquiv _ _
    ((ιj j ≫ sumTensorDesc σ V A b) ≫ d₀) = a j
  rw [Adjunction.homEquiv_naturality_right]
  simp only [ιj, sumTensorDesc, biproduct.ι_desc, Equiv.apply_symm_apply]
  exact hb j

/-! ### `Ext` out of `Φ P_v` as cohomology of sections over the star -/

/-- `extMk` depends only on the morphism. -/
private theorem extMk_eq_of_eq {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine}
    {X : TopCat.Sheaf (ModuleCat.{0} k) realLine} (R : InjectiveResolution Y) {n m : ℕ}
    (hm : n + 1 = m) {f g : X ⟶ R.cocomplex.X n} (hf : f ≫ R.cocomplex.d n m = 0)
    (hg : g ≫ R.cocomplex.d n m = 0) (h : f = g) :
    R.extMk f m hm hf = R.extMk g m hm hg := by
  subst h
  rfl

/-- The `Ext` class of a cocycle of sections over the star, through the universal property and
Mathlib's `InjectiveResolution.extMk`. -/
noncomputable def extOfStarCocycle (hp : StrictMono p) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine} (R : InjectiveResolution Y) (q : ℕ) :
    starCocycles k p v R (q + 1) →+
      Abelian.Ext ((extension k hp).obj (representable k (orient m) v)) Y (q + 1) where
  toFun z := R.extMk ((homExtensionRepresentableEquiv k hp v _).symm z.1) (q + 2) rfl
    (homExtensionRepresentableEquiv_symm_comp_d k hp v R q z)
  map_zero' := (extMk_eq_of_eq k R rfl _ (by simp) (by
      rw [ZeroMemClass.coe_zero, Equiv.symm_apply_eq, homExtensionRepresentableEquiv_zero])).trans
    (R.extMk_zero _ _)
  map_add' z w := (extMk_eq_of_eq k R rfl _ (by
      rw [Preadditive.add_comp, homExtensionRepresentableEquiv_symm_comp_d,
        homExtensionRepresentableEquiv_symm_comp_d, add_zero]) (by
      rw [Submodule.coe_add, Equiv.symm_apply_eq, homExtensionRepresentableEquiv_add,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply])).trans
    (R.add_extMk _ _ _ _ _ _).symm

theorem extOfStarCocycle_apply (hp : StrictMono p) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine} (R : InjectiveResolution Y) (q : ℕ)
    (z : starCocycles k p v R (q + 1)) :
    extOfStarCocycle k hp v R q z =
      R.extMk ((homExtensionRepresentableEquiv k hp v _).symm z.1) (q + 2) rfl
        (homExtensionRepresentableEquiv_symm_comp_d k hp v R q z) :=
  rfl

/-- Every class in `Ext^{q+1}(Φ P_v, Y)` comes from a cocycle of sections over the star. -/
theorem extOfStarCocycle_surjective (hp : StrictMono p) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine} (R : InjectiveResolution Y) (q : ℕ) :
    Function.Surjective (extOfStarCocycle k hp v R q) := by
  intro e
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective e (q + 2) rfl
  have hz : homExtensionRepresentableEquiv k hp v _ f ∈ starCocycles k p v R (q + 1) := by
    refine LinearMap.mem_ker.2 ?_
    change (R.cocomplex.d (q + 1) (q + 2)).hom.app _ (homExtensionRepresentableEquiv k hp v _ f) = 0
    rw [← homExtensionRepresentableEquiv_comp, hf, homExtensionRepresentableEquiv_zero]
  exact ⟨⟨_, hz⟩, extMk_eq_of_eq k R rfl
    (homExtensionRepresentableEquiv_symm_comp_d k hp v R q ⟨_, hz⟩) hf (Equiv.symm_apply_apply _ _)⟩

/-- A cocycle of sections over the star has vanishing `Ext` class exactly when it is a
coboundary. -/
theorem extOfStarCocycle_eq_zero_iff (hp : StrictMono p) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine} (R : InjectiveResolution Y) (q : ℕ)
    (z : starCocycles k p v R (q + 1)) :
    extOfStarCocycle k hp v R q z = 0 ↔ z.1 ∈ starCoboundaries k p v R q := by
  rw [extOfStarCocycle_apply, R.extMk_eq_zero_iff _ (q + 2) rfl _ q rfl]
  constructor
  · rintro ⟨g, hg⟩
    refine LinearMap.mem_range.2 ⟨homExtensionRepresentableEquiv k hp v _ g, ?_⟩
    change (R.cocomplex.d q (q + 1)).hom.app _ (homExtensionRepresentableEquiv k hp v _ g) = z.1
    rw [← homExtensionRepresentableEquiv_comp, hg, Equiv.apply_symm_apply]
  · intro hz
    obtain ⟨t, ht⟩ := LinearMap.mem_range.1 hz
    refine ⟨(homExtensionRepresentableEquiv k hp v _).symm t,
      (homExtensionRepresentableEquiv k hp v _).injective ?_⟩
    rw [homExtensionRepresentableEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact ht

/-- **`Ext^{q+1}(Φ P_v, Y)` is the cohomology of the sections over the open star.** For every
sheaf `Y` of `k`-modules on `ℝ` and every injective resolution `R` of `Y`, the `Ext` class map
`extOfStarCocycle` induces an isomorphism from the cohomology in degree `q + 1` of the complex
of sections of `R` over `star p v` to `Ext^{q+1}(Φ P_v, Y)`. -/
noncomputable def extStarEquiv (hp : StrictMono p) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine} (R : InjectiveResolution Y) (q : ℕ) :
    starCohomology k p v R q ≃+
      Abelian.Ext ((extension k hp).obj (representable k (orient m) v)) Y (q + 1) :=
  AddEquiv.ofBijective
    (QuotientAddGroup.lift _ (extOfStarCocycle k hp v R q)
      fun z hz => (AddMonoidHom.mem_ker).2 ((extOfStarCocycle_eq_zero_iff k hp v R q z).2 hz))
    ⟨(injective_iff_map_eq_zero _).2 fun x hx => by
        obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
        rw [QuotientAddGroup.lift_mk] at hx
        exact (QuotientAddGroup.eq_zero_iff z).2 ((extOfStarCocycle_eq_zero_iff k hp v R q z).1 hx),
      fun e => by
        obtain ⟨z, rfl⟩ := extOfStarCocycle_surjective k hp v R q e
        exact ⟨z, QuotientAddGroup.lift_mk _ _ _⟩⟩

/-- `extStarEquiv` sends the class of a cocycle to its `Ext` class. -/
theorem extStarEquiv_mk (hp : StrictMono p) (v : Fin (2 * m + 1))
    {Y : TopCat.Sheaf (ModuleCat.{0} k) realLine} (R : InjectiveResolution Y) (q : ℕ)
    (z : starCocycles k p v R (q + 1)) :
    extStarEquiv k hp v R q (z : starCohomology k p v R q) = extOfStarCocycle k hp v R q z :=
  rfl

end Ext

end TDA.Sheaf.RealConstructible
