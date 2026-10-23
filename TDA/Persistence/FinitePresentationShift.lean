import TDA.Persistence.GradedFreeShift
import TDA.Persistence.FinitePresentation
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Shifting finite presentations

The generator and relation families shift by subtracting the real parameter
from every grade. The relation map is transported through the free-module
shift isomorphisms. Reindexing preserves cokernels, giving an actual natural
isomorphism between the presented quotient and the shifted original quotient.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence NNReal

variable {R : Type u} [Ring R] {n : ℕ}

private instance shift_preservesZeroMorphisms (ε : ℝ≥0) :
    (CoordinateShift.shift (R := R) (n := n) ε).PreservesZeroMorphisms where
  map_zero _ _ := by
    apply NatTrans.ext
    funext a
    rfl

private instance shift_preservesCokernel (ε : ℝ≥0)
    {M N : PModule.{u,0,w} R (Fin n → ℝ)} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (CoordinateShift.shift ε) := by
  change PreservesColimit (parallelPair f 0)
    ((Functor.whiskeringLeft (Fin n → ℝ) (Fin n → ℝ) (ModuleCat.{w} R)).obj
      (CoordinateShift.translation ε).toFunctor)
  infer_instance

/-- Shift a presentation by transporting its homogeneous relation map through
the natural free-module shift isomorphisms. -/
noncomputable def Presentation.shift (ε : ℝ≥0)
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ)) :
    Presentation.{u,0,w} (R := R) (P := Fin n → ℝ) where
  generators := D.generators.shiftGrade (ε : ℝ)
  relations := D.relations.shiftGrade (ε : ℝ)
  relationMap :=
    (shiftIso (R := R) ε D.relations).hom ≫
      (CoordinateShift.shift ε).map D.relationMap ≫
      (shiftIso (R := R) ε D.generators).inv

/-- The shifted relation map commutes with both free-module identifications. -/
theorem Presentation.shift_relationMap_square (ε : ℝ≥0)
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ)) :
    (D.shift ε).relationMap ≫ (shiftIso (R := R) ε D.generators).hom =
      (shiftIso (R := R) ε D.relations).hom ≫
        (CoordinateShift.shift ε).map D.relationMap := by
  simp [Presentation.shift, Category.assoc]

/-- Shifting a presentation does not change either indexing family. -/
theorem Presentation.shift_finite (ε : ℝ≥0)
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ))
    (hD : D.IsFinite) : (D.shift ε).IsFinite := hD

/-- The quotient of the shifted presentation is naturally the diagonal shift
of the original quotient. This uses preservation of the cokernel by reindexing. -/
noncomputable def Presentation.presentedShiftIso (ε : ℝ≥0)
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ)) :
    (D.shift ε).presented ≅ (CoordinateShift.shift ε).obj D.presented :=
  cokernel.mapIso (f := (D.shift ε).relationMap)
      ((CoordinateShift.shift ε).map D.relationMap)
      (shiftIso (R := R) ε D.relations)
      (shiftIso (R := R) ε D.generators)
      (D.shift_relationMap_square ε) ≪≫
    (PreservesCokernel.iso (CoordinateShift.shift ε) D.relationMap).symm

/-- Under the quotient shift isomorphism, the new free cover is the shifted
old cover preceded by the free-module shift isomorphism. -/
theorem Presentation.cover_presentedShiftIso (ε : ℝ≥0)
    (D : Presentation.{u,0,w} (R := R) (P := Fin n → ℝ)) :
    (D.shift ε).cover ≫ (D.presentedShiftIso ε).hom =
      (shiftIso (R := R) ε D.generators).hom ≫
        (CoordinateShift.shift ε).map D.cover := by
  let c := cokernel.mapIso (f := (D.shift ε).relationMap)
    ((CoordinateShift.shift ε).map D.relationMap)
    (shiftIso (R := R) ε D.relations)
    (shiftIso (R := R) ε D.generators)
    (D.shift_relationMap_square ε)
  let p := PreservesCokernel.iso (CoordinateShift.shift ε) D.relationMap
  have hc : (D.shift ε).cover ≫ c.hom =
      (shiftIso (R := R) ε D.generators).hom ≫
        cokernel.π ((CoordinateShift.shift ε).map D.relationMap) := by
    change cokernel.π (D.shift ε).relationMap ≫ c.hom = _
    dsimp [c, cokernel.mapIso, cokernel.map]
    rw [cokernel.π_desc]
    rfl
  have hp : (CoordinateShift.shift ε).map (cokernel.π D.relationMap) ≫ p.hom =
      cokernel.π ((CoordinateShift.shift ε).map D.relationMap) :=
    PreservesCokernel.π_iso_hom (CoordinateShift.shift ε) D.relationMap
  change (D.shift ε).cover ≫ (c ≪≫ p.symm).hom =
    (shiftIso (R := R) ε D.generators).hom ≫
      (CoordinateShift.shift ε).map D.cover
  apply (cancel_mono p.hom).mp
  change (((D.shift ε).cover ≫ c.hom) ≫ p.inv) ≫ p.hom =
    ((shiftIso (R := R) ε D.generators).hom ≫
      (CoordinateShift.shift ε).map (cokernel.π D.relationMap)) ≫ p.hom
  simp only [Category.assoc, p.inv_hom_id, Category.comp_id]
  rw [hc]
  change (shiftIso (R := R) ε D.generators).hom ≫
      cokernel.π ((CoordinateShift.shift ε).map D.relationMap) =
    ((shiftIso (R := R) ε D.generators).hom ≫
      (CoordinateShift.shift ε).map (cokernel.π D.relationMap)) ≫ p.hom
  rw [Category.assoc, hp]

/-- Diagonal shifts preserve the existence of a finite presentation. -/
theorem finitelyPresented_shift (ε : ℝ≥0)
    {M : PModule.{u,0,max u w} R (Fin n → ℝ)}
    (hM : FinitelyPresented (R := R) (P := Fin n → ℝ) M) :
    FinitelyPresented (R := R) (P := Fin n → ℝ)
      ((CoordinateShift.shift ε).obj M) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  exact ⟨D.shift ε, D.shift_finite ε hD,
    ⟨(D.presentedShiftIso ε) ≪≫ (CoordinateShift.shift ε).mapIso e⟩⟩

end TDA.Persistence.GradedFree
