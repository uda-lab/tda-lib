import TDA.Persistence.FinitePresentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Structure maps away from presentation grades

For a presented module, a structure map is invertible whenever the generator
and relation free modules have the same available basis vectors at both ends.
This is the algebraic form of the no-critical-grade step in Lesnick's closure
argument (Lemma 6.4). The argument applies to any preorder and ring.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- If no generator or relation becomes available between `a` and `b`, the
presented module's transition is an isomorphism. -/
theorem Presentation.structureMap_isIso_of_birth_iff
    (D : Presentation.{u,v,w} (R := R) (P := P)) {a b : P} (hab : a ≤ b)
    (hG : ∀ g : D.generators.Carrier,
      D.generators.grade g ≤ a ↔ D.generators.grade g ≤ b)
    (hY : ∀ y : D.relations.Carrier,
      D.relations.grade y ≤ a ↔ D.relations.grade y ≤ b) :
    IsIso (structureMap D.presented hab) := by
  let evA := (evaluation P (ModuleCat.{max u w} R)).obj a
  let evB := (evaluation P (ModuleCat.{max u w} R)).obj b
  let eA := PreservesCokernel.iso evA D.relationMap
  let eB := PreservesCokernel.iso evB D.relationMap
  let gIso := structureIsoOfBirthIff (R := R) D.generators hab hG
  let yIso := structureIsoOfBirthIff (R := R) D.relations hab hY
  have hs : D.relationMap.app a ≫ gIso.hom =
      yIso.hom ≫ D.relationMap.app b :=
    (D.relationMap.naturality (homOfLE hab)).symm
  let cIso := cokernel.mapIso (f := D.relationMap.app a)
    (D.relationMap.app b) yIso gIso hs
  have hkey : structureMap D.presented hab ≫ eB.hom = eA.hom ≫ cIso.hom := by
    have hcover : Epi (D.cover.app a) :=
      (ModuleCat.epi_iff_surjective _).mpr (D.cover_surjective a)
    apply (cancel_epi (D.cover.app a)).mp
    have ha : D.cover.app a ≫ eA.hom = cokernel.π (D.relationMap.app a) := by
      exact PreservesCokernel.π_iso_hom evA D.relationMap
    have hb : D.cover.app b ≫ eB.hom = cokernel.π (D.relationMap.app b) := by
      exact PreservesCokernel.π_iso_hom evB D.relationMap
    have hn : D.cover.app a ≫ structureMap D.presented hab =
        gIso.hom ≫ D.cover.app b :=
      (D.cover.naturality (homOfLE hab)).symm
    calc
      D.cover.app a ≫ (structureMap D.presented hab ≫ eB.hom) =
          (D.cover.app a ≫ structureMap D.presented hab) ≫ eB.hom := by
            exact (Category.assoc _ _ _).symm
      _ = (gIso.hom ≫ D.cover.app b) ≫ eB.hom := by rw [hn]
      _ = gIso.hom ≫ cokernel.π (D.relationMap.app b) := by
        exact (Category.assoc _ _ _).trans (congrArg (gIso.hom ≫ ·) hb)
      _ = cokernel.π (D.relationMap.app a) ≫ cIso.hom := by
        simp [cIso, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
      _ = D.cover.app a ≫ (eA.hom ≫ cIso.hom) := by
        exact (congrArg (· ≫ cIso.hom) ha.symm).trans (Category.assoc _ _ _)
  have hcomp : IsIso (eA.hom ≫ cIso.hom) :=
    IsIso.comp_isIso' eA.isIso_hom cIso.isIso_hom
  have htotal : IsIso (structureMap D.presented hab ≫ eB.hom) := by
    rw [hkey]
    exact hcomp
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (structureMap D.presented hab) eB.hom eB.isIso_hom htotal

end TDA.Persistence.GradedFree
