import TDA.Persistence.CrossPresentationConverse
import TDA.Persistence.CrossPresentationExamples
import TDA.Persistence.FinitePresentationShift

/-!
# Finite cross-presentation characterization examples

The consumers reconstruct a positive-parameter pair with a nonzero relation,
compare redundant presentations at zero, and include the actual zero module
and a zero coefficient ring in dimension zero.
-/

set_option autoImplicit false

namespace TDA.Persistence.GradedFree.CrossPresentationConverseExamples

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence NNReal ZeroObject

/-- Reconstruct finite shared data for the existing nonzero-relation example. -/
theorem reconstruct_nonzero_relation :
    ∃ C : CrossData (R := ℤ) (n := 1) 1, C.IsFinite ∧
      Nonempty (C.leftPresentation.presented ≅
        CrossPresentationExamples.delayedDeath.leftPresentation.presented) ∧
      Nonempty (C.rightPresentation.presented ≅
        CrossPresentationExamples.delayedDeath.rightPresentation.presented) :=
  finitelyPresented_exists_crossPresentation
    (CrossPresentationExamples.delayedDeath.leftPresentation.finitelyPresented
      CrossPresentationExamples.delayedDeath_finite.1)
    (CrossPresentationExamples.delayedDeath.rightPresentation.finitelyPresented
      CrossPresentationExamples.delayedDeath_finite.2)
    CrossPresentationExamples.delayedDeath.quotientInterleaving

private abbrev W := CrossPresentationExamples.oneGrade 0

private noncomputable abbrev basic : Presentation (R := ℚ) (P := Fin 1 → ℝ) :=
  zeroRelationPresentation W W

private theorem basic_finite : basic.IsFinite :=
  ⟨inferInstanceAs (Finite Unit), inferInstanceAs (Finite Unit)⟩

private noncomputable abbrev redundant := basic.adjoinRedundant W (fun _ => 0)

/-- A redundant generator and a redundant zero relation do not obstruct the
zero-parameter characterization over a field. -/
theorem zero_parameter_redundant :
    ∃ C : CrossData (R := ℚ) (n := 1) 0, C.IsFinite ∧
      Nonempty (C.leftPresentation.presented ≅ basic.presented) ∧
      Nonempty (C.rightPresentation.presented ≅ redundant.presented) := by
  let : Finite W.Carrier := inferInstanceAs (Finite Unit)
  exact finitelyPresented_exists_crossPresentation
    (basic.finitelyPresented basic_finite)
    (redundant.finitelyPresented (basic.adjoinRedundant_finite W (fun _ => 0) basic_finite))
    (CoordinateInterleaving.ofIso (basic.adjoinRedundantIso W (fun _ => 0)).symm)

private def emptyFamily (n : ℕ) : GradedGenerators (Fin n → ℝ) where
  Carrier := Empty
  grade := Empty.elim

private noncomputable abbrev zeroModule (n : ℕ) : PModule.{0,0,0} ℚ (Fin n → ℝ) :=
  (Functor.const (Fin n → ℝ)).obj (0 : ModuleCat.{0} ℚ)

private noncomputable def emptyFreeIsoZero (n : ℕ) :
    module (R := ℚ) (emptyFamily n) ≅ zeroModule n := by
  apply IsZero.iso
  · apply Functor.isZero
    intro a
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (fiber (R := ℚ) (emptyFamily n) a)
    constructor
    intro x y
    apply Subtype.ext
    apply Finsupp.ext
    intro g
    exact Empty.elim g
  · exact Functor.isZero _ (fun _ => isZero_zero (ModuleCat ℚ))

/-- The actual zero functor has a finite presentation with no generators. -/
theorem zero_finitelyPresented (n : ℕ) :
    FinitelyPresented (R := ℚ) (P := Fin n → ℝ)
      (zeroModule n) := by
  let : Finite (emptyFamily n).Carrier := inferInstanceAs (Finite Empty)
  exact finitelyPresented_of_iso (free_finitelyPresented (emptyFamily n)) (emptyFreeIsoZero n)

/-- The finite characterization includes the actual zero module in dimension zero. -/
theorem zero_module_zero_dimension (ε : ℝ≥0) :
    ∃ C : CrossData (R := ℚ) (n := 0) ε, C.IsFinite ∧
      Nonempty (C.leftPresentation.presented ≅ zeroModule 0) ∧
      Nonempty (C.rightPresentation.presented ≅ zeroModule 0) :=
  finitelyPresented_exists_crossPresentation (zero_finitelyPresented 0)
    (zero_finitelyPresented 0) (CoordinateInterleaving.refl ε _)

private def oneZeroGrade : GradedGenerators (Fin 0 → ℝ) where
  Carrier := Unit
  grade _ := Fin.elim0

/-- No nontrivial-ring or positive-dimension assumption is concealed in the
finite characterization. -/
theorem zero_ring_zero_dimension (ε : ℝ≥0) :
    ∃ C : CrossData (R := ZMod 1) (n := 0) ε, C.IsFinite ∧
      Nonempty (C.leftPresentation.presented ≅ module (R := ZMod 1) oneZeroGrade) ∧
      Nonempty (C.rightPresentation.presented ≅ module (R := ZMod 1) oneZeroGrade) := by
  let : Finite oneZeroGrade.Carrier := inferInstanceAs (Finite Unit)
  exact finitelyPresented_exists_crossPresentation (free_finitelyPresented oneZeroGrade)
    (free_finitelyPresented oneZeroGrade) (CoordinateInterleaving.refl ε _)

/-- A genuine positive-width interleaving over a field is accepted without
unfolding the cross-presentation construction. -/
theorem positive_field_shift :
    ∃ C : CrossData (R := ℚ) (n := 1) 1, C.IsFinite ∧
      Nonempty (C.leftPresentation.presented ≅ module (R := ℚ) W) ∧
      Nonempty (C.rightPresentation.presented ≅ module (R := ℚ) (W.shiftGrade (-1))) := by
  let : Finite W.Carrier := inferInstanceAs (Finite Unit)
  let : Finite (W.shiftGrade (-1)).Carrier := inferInstanceAs (Finite Unit)
  let i : CoordinateInterleaving 1 (module (R := ℚ) W)
      (module (R := ℚ) (W.shiftGrade (-1))) :=
    CoordinateInterleaving.ofApp (delayedShiftIso (R := ℚ) 1 W).hom
      (delayedAdvance 1 W)
      (by intro a; apply ModuleCat.hom_ext; rfl)
      (by intro a; apply ModuleCat.hom_ext; rfl)
  exact finitelyPresented_exists_crossPresentation (free_finitelyPresented W)
    (free_finitelyPresented (W.shiftGrade (-1))) i

/-- A consumer obtains finite quotients directly from finite primitive data. -/
theorem finite_quotients {ε : ℝ≥0} (C : CrossData (R := ℚ) (n := 1) ε)
    (hC : C.IsFinite) : C.leftPresentation.IsFinite ∧ C.rightPresentation.IsFinite :=
  C.finite hC

/-- Quotient/shift compatibility is available at zero and positive parameters. -/
noncomputable def shiftedQuotient (ε : ℝ≥0) :
    (basic.shift ε).presented ≅ (CoordinateShift.shift ε).obj basic.presented :=
  basic.presentedShiftIso ε

end TDA.Persistence.GradedFree.CrossPresentationConverseExamples
