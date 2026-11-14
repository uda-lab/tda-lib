import TDA.Persistence.FinitePresentation
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Order.GaloisConnection.Basic

/-!
# Reindexing finite presentations along a right adjoint

If an index map `f : Q →o P` has left adjoint `l`, a free generator born at
`p` restricts to a free generator born at `l p`. The adjunction identifies
the supported free fibres without changing the generator occurrences.
Transporting the relation map and preserving its actual cokernel gives a
presentation of the restricted module, with the same two finite carriers.
The coefficient ring and both index universes are independent.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w x

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]
    {Q : Type x} [Preorder Q]

/-- Change generator grades while retaining every generator occurrence. -/
def GradedGenerators.regrade (W : GradedGenerators.{v,w} P) (l : P → Q) :
    GradedGenerators.{x,w} Q where
  Carrier := W.Carrier
  grade := l ∘ W.grade

omit [Preorder P] [Preorder Q] in
/-- Regrading applies the specified function to each original birth. -/
@[simp] theorem GradedGenerators.regrade_grade (W : GradedGenerators.{v,w} P)
    (l : P → Q) (g : W.Carrier) : (W.regrade l).grade g = l (W.grade g) := rfl

variable (f : Q →o P) (l : P → Q) (h : GaloisConnection l f)

include h in
/-- The adjunction gives equality of the supported free fibres. -/
theorem fiber_regrade_eq (W : GradedGenerators.{v,w} P) (q : Q) :
    fiber (R := R) (W.regrade l) q = fiber W (f q) := by
  unfold fiber
  congr 1
  ext g
  exact h (W.grade g) q

/-- Restriction of a graded free module is free on the regraded occurrences.
Each component retains the underlying finitely supported combination. -/
noncomputable def reindexIso (W : GradedGenerators.{v,w} P) :
    module (R := R) (W.regrade l) ≅ reindex f (module W) where
  hom := {
    app q := ModuleCat.ofHom (Submodule.inclusion (fiber_regrade_eq f l h W q).le)
    naturality _ _ _ := by apply ModuleCat.hom_ext; rfl }
  inv := {
    app q := ModuleCat.ofHom (Submodule.inclusion (fiber_regrade_eq f l h W q).ge)
    naturality _ _ _ := by apply ModuleCat.hom_ext; rfl }
  hom_inv_id := by apply NatTrans.ext; funext q; apply ModuleCat.hom_ext; rfl
  inv_hom_id := by apply NatTrans.ext; funext q; apply ModuleCat.hom_ext; rfl

/-- The free comparison does not alter any generator coefficient. -/
@[simp] theorem reindexIso_hom_val (W : GradedGenerators.{v,w} P) (q : Q)
    (z : (module (R := R) (W.regrade l)).obj q) :
    (((reindexIso f l h W).hom.app q).hom z : fiber (R := R) W (f q)).val = z.val := rfl

/-- Each available regraded generator maps to the same original occurrence. -/
theorem reindexIso_generator (W : GradedGenerators.{v,w} P) (q : Q)
    (g : W.Carrier) (hg : (W.regrade l).grade g ≤ q) :
    ((reindexIso f l h W).hom.app q).hom (generator (R := R) (W.regrade l) g hg) =
      generator (R := R) W g ((h (W.grade g) q).mp hg) := by
  apply Subtype.ext
  rfl

private def reindexFunctor :
    PModule.{u,v,max u w} R P ⥤ PModule.{u,x,max u w} R Q :=
  (Functor.whiskeringLeft Q P (ModuleCat.{max u w} R)).obj f.toFunctor

private instance reindex_preservesZeroMorphisms :
    (reindexFunctor (R := R) f).PreservesZeroMorphisms where
  map_zero _ _ := by apply NatTrans.ext; funext q; rfl

private instance reindex_preservesCokernel
    {A B : PModule.{u,v,max u w} R P} (φ : A ⟶ B) :
    PreservesColimit (parallelPair φ 0) (reindexFunctor f) := by
  dsimp [reindexFunctor]
  infer_instance

/-- Restrict a presentation by regrading both carriers and conjugating the
actual reindexed relation morphism by the free-module comparisons. -/
noncomputable def Presentation.reindex
    (D : Presentation.{u,v,w} (R := R) (P := P)) :
    Presentation.{u,x,w} (R := R) (P := Q) where
  generators := D.generators.regrade l
  relations := D.relations.regrade l
  relationMap := (reindexIso f l h D.relations).hom ≫
    reindexNatTrans f D.relationMap ≫ (reindexIso f l h D.generators).inv

/-- The transported relation morphism commutes with the free comparisons. -/
theorem Presentation.reindex_relationMap_square
    (D : Presentation.{u,v,w} (R := R) (P := P)) :
    (D.reindex f l h).relationMap ≫ (reindexIso f l h D.generators).hom =
      (reindexIso f l h D.relations).hom ≫ reindexNatTrans f D.relationMap := by
  simp [Presentation.reindex, Category.assoc]

/-- Restricting a presentation retains the two finite occurrence carriers. -/
theorem Presentation.reindex_finite
    (D : Presentation.{u,v,w} (R := R) (P := P)) (hD : D.IsFinite) :
    (D.reindex f l h).IsFinite := hD

/-- The new presented cokernel is naturally the actual restriction of the
original presented cokernel. -/
noncomputable def Presentation.presentedReindexIso
    (D : Presentation.{u,v,w} (R := R) (P := P)) :
    (D.reindex f l h).presented ≅ TDA.Persistence.reindex f D.presented :=
  cokernel.mapIso (f := (D.reindex f l h).relationMap)
      ((reindexFunctor f).map D.relationMap)
      (reindexIso f l h D.relations) (reindexIso f l h D.generators)
      (D.reindex_relationMap_square f l h) ≪≫
    (PreservesCokernel.iso (reindexFunctor f) D.relationMap).symm

/-- The presented comparison identifies the free cover with its restriction,
preceded by the free-generator comparison. -/
theorem Presentation.cover_presentedReindexIso
    (D : Presentation.{u,v,w} (R := R) (P := P)) :
    (D.reindex f l h).cover ≫ (D.presentedReindexIso f l h).hom =
      (reindexIso f l h D.generators).hom ≫ reindexNatTrans f D.cover := by
  let c := cokernel.mapIso (f := (D.reindex f l h).relationMap)
    ((reindexFunctor f).map D.relationMap)
    (reindexIso f l h D.relations) (reindexIso f l h D.generators)
    (D.reindex_relationMap_square f l h)
  let p := PreservesCokernel.iso (reindexFunctor f) D.relationMap
  have hc : (D.reindex f l h).cover ≫ c.hom =
      (reindexIso f l h D.generators).hom ≫
        cokernel.π ((reindexFunctor f).map D.relationMap) := by
    change cokernel.π (D.reindex f l h).relationMap ≫ c.hom = _
    dsimp [c, cokernel.mapIso, cokernel.map]
    rw [cokernel.π_desc]
  have hp : (reindexFunctor f).map (cokernel.π D.relationMap) ≫ p.hom =
      cokernel.π ((reindexFunctor f).map D.relationMap) :=
    PreservesCokernel.π_iso_hom (reindexFunctor f) D.relationMap
  change (D.reindex f l h).cover ≫ (c ≪≫ p.symm).hom =
    (reindexIso f l h D.generators).hom ≫ (reindexFunctor f).map D.cover
  apply (cancel_mono p.hom).mp
  change (((D.reindex f l h).cover ≫ c.hom) ≫ p.inv) ≫ p.hom =
    ((reindexIso f l h D.generators).hom ≫
      (reindexFunctor f).map (cokernel.π D.relationMap)) ≫ p.hom
  simp only [Category.assoc, p.inv_hom_id, Category.comp_id]
  rw [hc]
  change (reindexIso f l h D.generators).hom ≫
      cokernel.π ((reindexFunctor f).map D.relationMap) =
    ((reindexIso f l h D.generators).hom ≫
      (reindexFunctor f).map (cokernel.π D.relationMap)) ≫ p.hom
  rw [Category.assoc, hp]

include l h in
/-- Precomposition by a right adjoint preserves the original graded-free
finite-presentation predicate, including its generator-carrier universe. -/
theorem finitelyPresented_reindex_of_galoisConnection
    {M : PModule.{u,v,max u w} R P} (hM : FinitelyPresented.{u,v,w} M) :
    FinitelyPresented.{u,x,w} (reindex f M) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  exact ⟨D.reindex f l h, D.reindex_finite f l h hD,
    ⟨D.presentedReindexIso f l h ≪≫ (reindexFunctor f).mapIso e⟩⟩

end TDA.Persistence.GradedFree
