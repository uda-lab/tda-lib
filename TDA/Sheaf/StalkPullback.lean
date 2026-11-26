import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalks of the inverse image of a sheaf of modules

Let `k` be a ring and `f : X ⟶ Y` a continuous map in `TopCat`. The sheaf inverse image
`f⁻¹ = TopCat.Sheaf.pullback (ModuleCat k) f` is left adjoint to the direct image `f_*`
(`TopCat.Sheaf.pullbackPushforwardAdjunction`). Mathlib computes the stalks of the presheaf
inverse image (`TopCat.Presheaf.stalkPullbackIso`); this file transfers the computation to
sheaves.

* `pullbackPushforwardAdjunction_unit_app_hom`: the unit `F ⟶ f_* f⁻¹ F` of the sheaf adjunction
  is the unit of the presheaf adjunction, followed by sheafification and the comparison
  `TopCat.Sheaf.pullbackIso` of `f⁻¹` with the sheafified presheaf inverse image.
* `stalkPullbackSheafIso f F x : F_{f x} ≅ (f⁻¹ F)_x`, the stalk of the sheaf inverse image.
* `germ_stalkPullbackSheafIso_hom` and `stalkPullbackSheafIso_unit`: the isomorphism sends the
  germ at `f x` of a section `n` over `V` to the germ at `x` of the image of `n` under the
  adjunction unit.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable (k : Type) [Ring k]

/-- The unit of the sheaf adjunction `f⁻¹ ⊣ f_*` at `F` is the unit of the presheaf adjunction,
followed by sheafification of `f⁻¹ F` and the inverse of `TopCat.Sheaf.pullbackIso`. -/
theorem pullbackPushforwardAdjunction_unit_app_hom {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : Y.Sheaf (ModuleCat.{0} k)) :
    (TopCat.Presheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F.presheaf ≫
      (TopCat.Presheaf.pushforward _ f).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback (ModuleCat.{0} k) f).obj F.presheaf) ≫
            ((TopCat.Sheaf.pullbackIso (ModuleCat.{0} k) f).inv.app F).hom) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) (ModuleCat.{0} k)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f) F
  rw [← h]
  rfl

/-- **Stalks of the sheaf inverse image.** For a continuous map `f : X ⟶ Y`, a sheaf `F` of
`k`-modules on `Y` and `x : X`, the stalk of `f⁻¹ F` at `x` is the stalk of `F` at `f x`. -/
def stalkPullbackSheafIso {X Y : TopCat.{0}} (f : X ⟶ Y) (F : Y.Sheaf (ModuleCat.{0} k))
    (x : X) :
    F.presheaf.stalk (f x) ≅ ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj F).presheaf.stalk x :=
  TopCat.Presheaf.stalkPullbackIso _ f F.presheaf x ≪≫
    @asIso _ _ _ _ ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback (ModuleCat.{0} k) f).obj F.presheaf)))
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} k) _) ≪≫
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).mapIso
      ((sheafToPresheaf _ _).mapIso ((TopCat.Sheaf.pullbackIso (ModuleCat.{0} k) f).app F).symm)

/-- `stalkPullbackSheafIso` on germs: the germ of a section over `V` at `f x` goes to the germ at
`x` of its image under the adjunction unit `F ⟶ f_* f⁻¹ F`. -/
@[reassoc]
theorem germ_stalkPullbackSheafIso_hom {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : Y.Sheaf (ModuleCat.{0} k)) (V : Opens Y) (x : X) (hx : f x ∈ V) :
    F.presheaf.germ V (f x) hx ≫ (stalkPullbackSheafIso k f F x).hom =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom.app
          (op V) ≫
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj F).presheaf.germ
          ((Opens.map f).obj V) x hx := by
  rw [← pullbackPushforwardAdjunction_unit_app_hom]
  change F.presheaf.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom _ f F.presheaf x ≫
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback (ModuleCat.{0} k) f).obj F.presheaf)) ≫
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} k) x).map
      ((TopCat.Sheaf.pullbackIso (ModuleCat.{0} k) f).inv.app F).hom = _
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc]
  -- The membership proof `hx : f x ∈ V` is used at type `x ∈ (Opens.map f).obj V`, so the
  -- rewrite motive is only correct up to unfolding.
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- `stalkPullbackSheafIso` on elements: the germ of `n` at `f x` corresponds to the germ at `x`
of the image of `n` under the adjunction unit `F ⟶ f_* f⁻¹ F`. -/
theorem stalkPullbackSheafIso_unit {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : Y.Sheaf (ModuleCat.{0} k)) (V : Opens Y) (x : X) (hx : f x ∈ V)
    (n : F.presheaf.obj (op V)) :
    (stalkPullbackSheafIso k f F x).hom (F.presheaf.germ V (f x) hx n) =
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj F).presheaf.germ ((Opens.map f).obj V) x hx
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom.app
          (op V) n) :=
  ConcreteCategory.congr_hom (germ_stalkPullbackSheafIso_hom k f F V x hx) n

end TDA.Sheaf
