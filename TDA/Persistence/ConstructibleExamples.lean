import TDA.Persistence.Constructible
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Finite-stratum reconstruction examples

An empty grid reconstructs a zero module. A one-value grid includes its critical endpoint and
has an unbounded nonzero final tail. A change of coordinates by a factor of two produces an
nonidentity transition within that single tail cell.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteConstructibleExamples

open CategoryTheory CategoryTheory.Limits FiniteConstructible
open scoped ZeroObject

private def emptyGrid : Fin 0 ↪o ℝ :=
  ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, fun {i} => Fin.elim0 i⟩

private def oneGrid : Fin 1 ↪o ℝ where
  toFun _ := 0
  inj' _ _ _ := Subsingleton.elim _ _
  map_rel_iff' := by intro i j; simp [Subsingleton.elim i j]

private noncomputable def zeroModule : PModule.{0,0,0} ℤ ℝ :=
  (Functor.const ℝ).obj (0 : ModuleCat.{0} ℤ)

/-- No critical values give a natural isomorphism to the zero module. -/
noncomputable def emptyReconstruction :
    reindex (cellIndex emptyGrid) (sample emptyGrid zeroModule) ≅ zeroModule :=
  reconstructionIso emptyGrid zeroModule
    ((isConstructible_empty_iff emptyGrid zeroModule).mpr
      (fun _ => isZero_zero (ModuleCat ℤ)))

private noncomputable def constantRationals : PModule.{0,0,0} ℚ ℝ :=
  (Functor.const ℝ).obj (ModuleCat.of ℚ ℚ)

private noncomputable def stepModule : PModule ℚ ℝ :=
  reindex (cellIndex oneGrid) (sample oneGrid constantRationals)

private theorem step_constructible : IsConstructible oneGrid stepModule :=
  isConstructible_reindex oneGrid _ (isZero_zero (ModuleCat ℚ))

/-- The exact critical value is in the positive cell; the left parameter is in the zero cell. -/
theorem critical_and_left_cells :
    cellIndex oneGrid 0 = 1 ∧ cellIndex oneGrid (-1) = 0 := by
  constructor
  · exact cellIndex_critical oneGrid 0
  · apply (cellIndex_eq_zero_iff oneGrid (-1)).mpr
    intro i
    change (-1 : ℝ) < 0
    norm_num

/-- The final cell contains every nonnegative real parameter. -/
theorem unbounded_final_cell (t : ℝ) (ht : 0 ≤ t) : cellIndex oneGrid t = 1 :=
  cellIndex_of_last_le oneGrid t ht

/-- The entire left ray has zero fibers. -/
theorem step_zero_left (t : ℝ) (ht : t < 0) : IsZero (stepModule.obj t) :=
  step_constructible.zero_left t (fun _ => ht)

/-- The final cell retains a nonzero fiber, with no terminal vanishing assumption. -/
theorem step_nonzero_tail (t : ℝ) (ht : 0 ≤ t) : ¬ IsZero (stepModule.obj t) := by
  change ¬ IsZero ((sample oneGrid constantRationals).obj (cellIndex oneGrid t))
  rw [unbounded_final_cell t ht]
  change ¬ IsZero (ModuleCat.of ℚ ℚ)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact not_subsingleton ℚ

private noncomputable def coordinateChange (t : ℝ) : stepModule.obj t ≅ stepModule.obj t :=
  (LinearEquiv.smulOfNeZero ℚ (stepModule.obj t) (if t < 1 then 1 else 2)
    (by split_ifs <;> norm_num)).toModuleIso

-- Conjugation changes maps while keeping the fibers and zero left tail.
private noncomputable def twistedStep : PModule ℚ ℝ where
  obj := stepModule.obj
  map {s t} f := (coordinateChange s).inv ≫ stepModule.map f ≫ (coordinateChange t).hom
  map_id s := by simp
  map_comp f g := by simp [Category.assoc]

private theorem twisted_constructible : IsConstructible oneGrid twistedStep where
  zero_left := step_constructible.zero_left
  isIso_map s t h heq := by
    have := step_constructible.isIso_map s t h heq
    change IsIso ((coordinateChange s).inv ≫ structureMap stepModule h ≫
      (coordinateChange t).hom)
    infer_instance

/-- Reconstruction applies even when within-cell maps are not identities. -/
noncomputable def twistedReconstruction :
    reindex (cellIndex oneGrid) (sample oneGrid twistedStep) ≅ twistedStep :=
  reconstructionIso oneGrid twistedStep twisted_constructible

/-- Inside one cell, the transition differs from the base step's identity transition:
the change of coordinates multiplies it by two. -/
theorem twisted_transition_nonidentity :
    structureMap twistedStep (show (0 : ℝ) ≤ 1 by norm_num) ≠
      structureMap stepModule (show (0 : ℝ) ≤ 1 by norm_num) := by
  intro h
  have he : coordinateChange 0 = Iso.refl _ := by
    ext x
    simp [coordinateChange]
  have hcells : cellIndex oneGrid 0 = cellIndex oneGrid 1 := by
    rw [unbounded_final_cell 0 le_rfl, unbounded_final_cell 1 (by norm_num)]
  have := step_constructible.isIso_map 0 1 (by norm_num) hcells
  change (coordinateChange 0).inv ≫ structureMap stepModule _ ≫
    (coordinateChange 1).hom = structureMap stepModule _ at h
  rw [he, Iso.refl_inv, Category.id_comp] at h
  have hh : (coordinateChange 1).hom = 𝟙 _ := by
    apply (cancel_epi (structureMap stepModule (show (0 : ℝ) ≤ 1 by norm_num))).mp
    simpa using h
  apply step_nonzero_tail 1 (by norm_num)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hz (x : stepModule.obj 1) : x = 0 := by
    have hx := congrArg (fun f : stepModule.obj 1 ⟶ stepModule.obj 1 => f.hom x) hh
    change (if (1 : ℝ) < 1 then (1 : ℚ) else 2) • x = x at hx
    have hx' : x + x = x := by simpa [two_smul] using hx
    exact add_left_cancel (hx'.trans (add_zero x).symm)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Equal one-dimensional fibers do not make the zero transition an isomorphism. -/
theorem zero_transition_not_isIso :
    ¬ IsIso (structureMap (zeroTransitionDiagram ℚ)
      (show (0 : Fin 2) ≤ 1 by decide)) := by
  intro h
  have := h
  have he := (asIso (structureMap (zeroTransitionDiagram ℚ)
    (show (0 : Fin 2) ≤ 1 by decide))).hom_inv_id
  change (0 : (zeroTransitionDiagram ℚ).obj 0 ⟶
    (zeroTransitionDiagram ℚ).obj 1) ≫ _ = 𝟙 _ at he
  rw [zero_comp] at he
  have hv := congrArg (fun f : (zeroTransitionDiagram ℚ).obj 0 ⟶
    (zeroTransitionDiagram ℚ).obj 0 => f.hom (1 : ℚ)) he
  change (0 : ℚ) = 1 at hv
  norm_num at hv

end TDA.Persistence.FiniteConstructibleExamples
