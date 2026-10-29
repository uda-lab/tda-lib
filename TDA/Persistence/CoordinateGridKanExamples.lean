import TDA.Persistence.CoordinateGridRankExact
import TDA.Persistence.FiniteHookDeflation
import TDA.Persistence.HookInfinity
import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Finite-grid Kan extension consumers

These examples follow actual fibers and maps of Mathlib's left Kan extension.
The planar fixture has a finite-death hook quotient with a nonzero vector that
dies across grid cells; its real-grade lift is supplied by rank exactness.
-/

set_option autoImplicit false

namespace TDA.Persistence.CoordinateGridKan.Examples

open CategoryTheory
open CategoryTheory.Limits
open scoped TDA.Persistence ZeroObject

noncomputable def planarGrid : CoordinateGrid 2 := by
  classical
  exact fun _ => {0, 2}

noncomputable def planarLower : planarGrid.Point := fun _ => ⟨0, by simp [planarGrid]⟩

noncomputable def planarUpper : planarGrid.Point := fun _ => ⟨2, by simp [planarGrid]⟩

noncomputable def gradeA : Fin 2 → ℝ := fun _ => 1 / 2

noncomputable def gradeC : Fin 2 → ℝ := fun _ => 1

noncomputable def gradeB : Fin 2 → ℝ := fun _ => 5 / 2

private theorem planar_mem (q : planarGrid.Point) (i : Fin 2) :
    (q i).val = 0 ∨ (q i).val = 2 := by
  have h : (q i).val ∈ ({(0 : ℝ), 2} : Finset ℝ) := by
    simpa [planarGrid] using (q i).property
  simpa using h

private theorem planarLower_le (q : planarGrid.Point) : planarLower ≤ q := by
  intro i
  change (0 : ℝ) ≤ (q i).val
  rcases planar_mem q i with h | h
  · norm_num [h]
  · norm_num [h]

private theorem q_le_planarUpper (q : planarGrid.Point) : q ≤ planarUpper := by
  intro i
  change (q i).val ≤ 2
  rcases planar_mem q i with h | h
  · norm_num [h]
  · norm_num [h]

theorem gradeA_hasLowerPoint : planarGrid.HasLowerPoint gradeA := by
  refine ⟨planarLower, ?_⟩
  intro i
  norm_num [CoordinateGrid.embedding_apply, planarLower, gradeA]

theorem gradeC_hasLowerPoint : planarGrid.HasLowerPoint gradeC := by
  refine ⟨planarLower, ?_⟩
  intro i
  norm_num [CoordinateGrid.embedding_apply, planarLower, gradeC]

theorem gradeB_hasLowerPoint : planarGrid.HasLowerPoint gradeB := by
  refine ⟨planarUpper, ?_⟩
  intro i
  norm_num [CoordinateGrid.embedding_apply, planarUpper, gradeB]

private theorem q_le_planarLower_of_le_gradeA (q : planarGrid.Point)
    (hq : planarGrid.embedding q ≤ gradeA) : q ≤ planarLower := by
  intro i
  have hqi := hq i
  change (q i).val ≤ 1 / 2 at hqi
  rcases planar_mem q i with h | h
  · change (q i).val ≤ 0
    rw [h]
  · rw [h] at hqi
    norm_num at hqi

private theorem q_le_planarLower_of_le_gradeC (q : planarGrid.Point)
    (hq : planarGrid.embedding q ≤ gradeC) : q ≤ planarLower := by
  intro i
  have hqi := hq i
  change (q i).val ≤ 1 at hqi
  rcases planar_mem q i with h | h
  · change (q i).val ≤ 0
    rw [h]
  · rw [h] at hqi
    norm_num at hqi

private theorem floor_gradeA : planarGrid.floor gradeA gradeA_hasLowerPoint = planarLower := by
  apply (planarGrid.floor_eq_iff gradeA gradeA_hasLowerPoint planarLower).2
  refine ⟨?_, ?_⟩
  · intro i
    norm_num [CoordinateGrid.embedding_apply, planarLower, gradeA]
  · intro q hq
    exact q_le_planarLower_of_le_gradeA q hq

private theorem floor_gradeC : planarGrid.floor gradeC gradeC_hasLowerPoint = planarLower := by
  apply (planarGrid.floor_eq_iff gradeC gradeC_hasLowerPoint planarLower).2
  refine ⟨?_, ?_⟩
  · intro i
    norm_num [CoordinateGrid.embedding_apply, planarLower, gradeC]
  · intro q hq
    exact q_le_planarLower_of_le_gradeC q hq

private theorem floor_gradeB : planarGrid.floor gradeB gradeB_hasLowerPoint = planarUpper := by
  apply (planarGrid.floor_eq_iff gradeB gradeB_hasLowerPoint planarUpper).2
  refine ⟨?_, ?_⟩
  · intro i
    norm_num [CoordinateGrid.embedding_apply, planarUpper, gradeB]
  · intro q _
    exact q_le_planarUpper q

private theorem planarLower_lt_upper : planarLower < planarUpper := by
  apply lt_of_le_of_ne
  · intro i
    change (0 : ℝ) ≤ 2
    norm_num
  · intro h
    have h0 := congrArg (fun p : planarGrid.Point => (p 0).val) h
    norm_num [planarLower, planarUpper] at h0

noncomputable abbrev finiteHook (k : Type) [Field k] :
    PModule k planarGrid.Point := Hook.module planarLower planarUpper

private noncomputable def finiteHookDyingVector (k : Type) [Field k] :
    (finiteHook k).obj planarLower :=
  SupportInterval.one (Hook.support planarLower planarUpper)
    (Hook.birth_mem planarLower_lt_upper)

private theorem finiteHookDyingVector_ne_zero (k : Type) [Field k] :
    finiteHookDyingVector k ≠ 0 := by
  intro h
  have hval := congrArg Subtype.val h
  exact (one_ne_zero : (1 : k) ≠ 0) hval

private theorem finiteHookDyingVector_eq_unit (k : Type) [Field k] :
    finiteHookDyingVector k =
      SupportInterval.one (Hook.support planarLower planarUpper)
        (Hook.birth_mem planarLower_lt_upper) := by
  apply Subtype.ext
  rfl

private theorem gradeA_le_gradeC : gradeA ≤ gradeC := by
  intro i
  norm_num [gradeA, gradeC]

private theorem gradeC_le_gradeB : gradeC ≤ gradeB := by
  intro i
  norm_num [gradeC, gradeB]

private theorem gradeA_le_gradeB : gradeA ≤ gradeB := gradeA_le_gradeC.trans gradeC_le_gradeB

private noncomputable def floorHookVector (k : Type) [Field k]
    (a : Fin 2 → ℝ) (ha : planarGrid.HasLowerPoint a) :
    (finiteHook k).obj (planarGrid.floor a ha) :=
  structureMapLinear (finiteHook k) (planarLower_le (planarGrid.floor a ha))
    (finiteHookDyingVector k)

private theorem floorHookVector_ne_zero_of_floor (k : Type) [Field k]
    (a : Fin 2 → ℝ) (ha : planarGrid.HasLowerPoint a)
    (hf : planarGrid.floor a ha = planarLower) : floorHookVector k a ha ≠ 0 := by
  let hA := planarLower_le (planarGrid.floor a ha)
  let hBack : planarGrid.floor a ha ≤ planarLower := by
    rw [hf]
  intro hz
  have hcomp := structureMapLinear_comp (finiteHook k) hA hBack
  have hid := (structureMapLinear_self (finiteHook k) (hA.trans hBack)).symm.trans hcomp
  change structureMapLinear (finiteHook k) hA (finiteHookDyingVector k) = 0 at hz
  have hzero := congrArg (structureMapLinear (finiteHook k) hBack) hz
  have hvec : finiteHookDyingVector k = 0 := by
    calc
      finiteHookDyingVector k =
          (structureMapLinear (finiteHook k) hBack)
            ((structureMapLinear (finiteHook k) hA) (finiteHookDyingVector k)) := by
              have heq := congrArg (fun f => f (finiteHookDyingVector k)) hid
              simpa only [LinearMap.id_apply, LinearMap.comp_apply] using heq
      _ = 0 := by simpa only [map_zero] using hzero
  exact finiteHookDyingVector_ne_zero k hvec

private theorem floorHookVectorA_ne_zero (k : Type) [Field k] :
    floorHookVector k gradeA gradeA_hasLowerPoint ≠ 0 :=
  floorHookVector_ne_zero_of_floor k gradeA gradeA_hasLowerPoint floor_gradeA

private theorem floorHookVectorC_ne_zero (k : Type) [Field k] :
    floorHookVector k gradeC gradeC_hasLowerPoint ≠ 0 :=
  floorHookVector_ne_zero_of_floor k gradeC gradeC_hasLowerPoint floor_gradeC

private theorem floorHookVector_between (k : Type) [Field k] :
    structureMapLinear (finiteHook k)
      (planarGrid.floor_mono gradeA_le_gradeC gradeA_hasLowerPoint gradeC_hasLowerPoint)
      (floorHookVector k gradeA gradeA_hasLowerPoint) =
        floorHookVector k gradeC gradeC_hasLowerPoint := by
  let hA := planarLower_le (planarGrid.floor gradeA gradeA_hasLowerPoint)
  let hAC := planarGrid.floor_mono gradeA_le_gradeC gradeA_hasLowerPoint gradeC_hasLowerPoint
  let hC := planarLower_le (planarGrid.floor gradeC gradeC_hasLowerPoint)
  change structureMapLinear (finiteHook k) hAC
      (structureMapLinear (finiteHook k) hA (finiteHookDyingVector k)) =
    structureMapLinear (finiteHook k) hC (finiteHookDyingVector k)
  have hrel : hA.trans hAC = hC := Subsingleton.elim _ _
  calc
    structureMapLinear (finiteHook k) hAC
        (structureMapLinear (finiteHook k) hA (finiteHookDyingVector k)) =
        (structureMapLinear (finiteHook k) hAC).comp
          (structureMapLinear (finiteHook k) hA) (finiteHookDyingVector k) := rfl
    _ = structureMapLinear (finiteHook k) (hA.trans hAC) (finiteHookDyingVector k) := by
      rw [← structureMapLinear_comp]
    _ = structureMapLinear (finiteHook k) hC (finiteHookDyingVector k) := by rw [hrel]

private theorem floorHookVector_dies (k : Type) [Field k] :
    structureMapLinear (finiteHook k)
      (planarGrid.floor_mono gradeC_le_gradeB gradeC_hasLowerPoint gradeB_hasLowerPoint)
      (floorHookVector k gradeC gradeC_hasLowerPoint) = 0 := by
  let hC := planarLower_le (planarGrid.floor gradeC gradeC_hasLowerPoint)
  let hCB := planarGrid.floor_mono gradeC_le_gradeB gradeC_hasLowerPoint gradeB_hasLowerPoint
  let hB := planarLower_le (planarGrid.floor gradeB gradeB_hasLowerPoint)
  change structureMapLinear (finiteHook k) hCB
      (structureMapLinear (finiteHook k) hC (finiteHookDyingVector k)) = 0
  have hrel : hC.trans hCB = hB := Subsingleton.elim _ _
  calc
    structureMapLinear (finiteHook k) hCB
        (structureMapLinear (finiteHook k) hC (finiteHookDyingVector k)) =
        (structureMapLinear (finiteHook k) hCB).comp
          (structureMapLinear (finiteHook k) hC) (finiteHookDyingVector k) := rfl
    _ = structureMapLinear (finiteHook k) (hC.trans hCB) (finiteHookDyingVector k) := by
      rw [← structureMapLinear_comp]
    _ = structureMapLinear (finiteHook k) hB (finiteHookDyingVector k) := by rw [hrel]
    _ = 0 := by
      change structureMapLinear (finiteHook k)
        (planarLower_le (planarGrid.floor gradeB gradeB_hasLowerPoint))
        (finiteHookDyingVector k) = 0
      rw [floor_gradeB]
      rw [finiteHookDyingVector_eq_unit]
      exact Hook.generator_dies planarLower_lt_upper (𝟙 (finiteHook k))

private theorem floorHookVector_dies_from_A (k : Type) [Field k] :
    structureMapLinear (finiteHook k)
      (planarGrid.floor_mono gradeA_le_gradeB gradeA_hasLowerPoint gradeB_hasLowerPoint)
      (floorHookVector k gradeA gradeA_hasLowerPoint) = 0 := by
  let hA := planarLower_le (planarGrid.floor gradeA gradeA_hasLowerPoint)
  let hAB := planarGrid.floor_mono gradeA_le_gradeB gradeA_hasLowerPoint gradeB_hasLowerPoint
  let hC := planarLower_le (planarGrid.floor gradeC gradeC_hasLowerPoint)
  let hCB := planarGrid.floor_mono gradeC_le_gradeB gradeC_hasLowerPoint gradeB_hasLowerPoint
  change structureMapLinear (finiteHook k) hAB
      (structureMapLinear (finiteHook k) hA (finiteHookDyingVector k)) = 0
  have hrel : hA.trans hAB = hC.trans hCB := Subsingleton.elim _ _
  calc
    structureMapLinear (finiteHook k) hAB
        (structureMapLinear (finiteHook k) hA (finiteHookDyingVector k)) =
        (structureMapLinear (finiteHook k) hAB).comp
          (structureMapLinear (finiteHook k) hA) (finiteHookDyingVector k) := rfl
    _ = structureMapLinear (finiteHook k) (hA.trans hAB) (finiteHookDyingVector k) := by
      rw [← structureMapLinear_comp]
    _ = structureMapLinear (finiteHook k) (hC.trans hCB) (finiteHookDyingVector k) := by
      rw [hrel]
    _ = (structureMapLinear (finiteHook k) hCB).comp
        (structureMapLinear (finiteHook k) hC) (finiteHookDyingVector k) := by
      rw [structureMapLinear_comp]
    _ = structureMapLinear (finiteHook k) hCB
        (structureMapLinear (finiteHook k) hC (finiteHookDyingVector k)) := rfl
    _ = 0 := floorHookVector_dies k

/-- The finite-death hook's unit transported to the actual Lan fiber at grade A. -/
noncomputable def kanHookVector (k : Type) [Field k] :
    (planarGrid.lan.obj (finiteHook k)).obj gradeA :=
  (planarGrid.appIso (finiteHook k) gradeA gradeA_hasLowerPoint).inv.hom
    (floorHookVector k gradeA gradeA_hasLowerPoint)

/-- The same unit transported to the actual Lan fiber at grade C. -/
noncomputable def kanHookVectorAtC (k : Type) [Field k] :
    (planarGrid.lan.obj (finiteHook k)).obj gradeC :=
  (planarGrid.appIso (finiteHook k) gradeC gradeC_hasLowerPoint).inv.hom
    (floorHookVector k gradeC gradeC_hasLowerPoint)

/-- The real-grade vector remains nonzero in its actual Kan fiber. -/
theorem kanHookVector_ne_zero (k : Type) [Field k] : kanHookVector k ≠ 0 := by
  intro hz
  have heq := congrArg
    (fun x => (planarGrid.appIso (finiteHook k) gradeA gradeA_hasLowerPoint).hom.hom x) hz
  have hfloor : floorHookVector k gradeA gradeA_hasLowerPoint = 0 := by
    simpa [kanHookVector] using heq
  exact floorHookVectorA_ne_zero k hfloor

/-- The within-cell image at grade C is nonzero as well. -/
theorem kanHookVectorAtC_ne_zero (k : Type) [Field k] : kanHookVectorAtC k ≠ 0 := by
  intro hz
  have heq := congrArg
    (fun x => (planarGrid.appIso (finiteHook k) gradeC gradeC_hasLowerPoint).hom.hom x) hz
  have hfloor : floorHookVector k gradeC gradeC_hasLowerPoint = 0 := by
    simpa [kanHookVectorAtC] using heq
  exact floorHookVectorC_ne_zero k hfloor

/-- The unit vector survives a transition within the first real grid cell. -/
theorem within_cell_transition_preserves_vector (k : Type) [Field k] :
    structureMapLinear (planarGrid.lan.obj (finiteHook k)) gradeA_le_gradeC
      (kanHookVector k) = kanHookVectorAtC k := by
  apply (planarGrid.appIso (finiteHook k) gradeC gradeC_hasLowerPoint).toLinearEquiv.injective
  change (planarGrid.appIso (finiteHook k) gradeC gradeC_hasLowerPoint).hom.hom
      (structureMapLinear (planarGrid.lan.obj (finiteHook k)) gradeA_le_gradeC
        (kanHookVector k)) =
      (planarGrid.appIso (finiteHook k) gradeC gradeC_hasLowerPoint).hom.hom
        (kanHookVectorAtC k)
  rw [planarGrid.appIso_structureMap_apply (M := finiteHook k)
    gradeA_le_gradeC gradeA_hasLowerPoint gradeC_hasLowerPoint]
  simpa [kanHookVector, kanHookVectorAtC] using floorHookVector_between k

/-- The actual real structure map kills the vector after crossing the hook death. -/
theorem across_cell_transition_kills_vector (k : Type) [Field k] :
    structureMapLinear (planarGrid.lan.obj (finiteHook k)) gradeC_le_gradeB
      (kanHookVectorAtC k) = 0 := by
  apply (planarGrid.appIso (finiteHook k) gradeB gradeB_hasLowerPoint).toLinearEquiv.injective
  change (planarGrid.appIso (finiteHook k) gradeB gradeB_hasLowerPoint).hom.hom
      (structureMapLinear (planarGrid.lan.obj (finiteHook k)) gradeC_le_gradeB
        (kanHookVectorAtC k)) =
      (planarGrid.appIso (finiteHook k) gradeB gradeB_hasLowerPoint).hom.hom 0
  rw [planarGrid.appIso_structureMap_apply (M := finiteHook k)
    gradeC_le_gradeB gradeC_hasLowerPoint gradeB_hasLowerPoint]
  simpa [kanHookVectorAtC] using floorHookVector_dies k

/-- Kan extension retains the actual map of the finite-hook quotient. -/
theorem quotient_map_at_gradeA (k : Type) [Field k]
    (m : (planarGrid.lan.obj (FiniteHookDeflation.module (finiteHook k))).obj gradeA) :
    (planarGrid.appIso (finiteHook k) gradeA gradeA_hasLowerPoint).hom.hom
        (((planarGrid.lan.map (FiniteHookDeflation.π (finiteHook k))).app gradeA).hom m) =
      ((FiniteHookDeflation.π (finiteHook k)).app
        (planarGrid.floor gradeA gradeA_hasLowerPoint)).hom
        ((planarGrid.appIso (FiniteHookDeflation.module (finiteHook k)) gradeA
          gradeA_hasLowerPoint).hom.hom m) := by
  exact planarGrid.appIso_map_apply (FiniteHookDeflation.π (finiteHook k)) gradeA
    gradeA_hasLowerPoint m

/-- A nonzero dying quotient vector has a nonzero lift dying at the same real grade. -/
theorem rankExact_lifts_nonzero_dying_vector (k : Type) [Field k] :
    ∃ m : (planarGrid.lan.obj (FiniteHookDeflation.module (finiteHook k))).obj gradeA,
      ((planarGrid.lan.map (FiniteHookDeflation.π (finiteHook k))).app gradeA).hom m =
          kanHookVector k ∧
        m ≠ 0 ∧
        structureMapLinear (planarGrid.lan.obj (FiniteHookDeflation.module (finiteHook k)))
          gradeA_le_gradeB m = 0 := by
  let hs := planarGrid.lan_isRankExact (FiniteHookDeflation.rankExact (finiteHook k))
  have hdie : structureMapLinear (planarGrid.lan.obj (finiteHook k)) gradeA_le_gradeB
      (kanHookVector k) = 0 := by
    have h := planarGrid.appIso_structureMap_apply (M := finiteHook k)
      gradeA_le_gradeB gradeA_hasLowerPoint gradeB_hasLowerPoint (kanHookVector k)
    have hzero : structureMapLinear (finiteHook k)
        (planarGrid.floor_mono gradeA_le_gradeB gradeA_hasLowerPoint gradeB_hasLowerPoint)
        ((planarGrid.appIso (finiteHook k) gradeA gradeA_hasLowerPoint).hom.hom
          (kanHookVector k)) = 0 := by
      simpa [kanHookVector] using floorHookVector_dies_from_A k
    apply (planarGrid.appIso (finiteHook k) gradeB gradeB_hasLowerPoint).toLinearEquiv.injective
    change (planarGrid.appIso (finiteHook k) gradeB gradeB_hasLowerPoint).hom.hom
        (structureMapLinear (planarGrid.lan.obj (finiteHook k)) gradeA_le_gradeB
          (kanHookVector k)) =
      (planarGrid.appIso (finiteHook k) gradeB gradeB_hasLowerPoint).hom.hom 0
    simpa only [map_zero] using h.trans hzero
  obtain ⟨m, hm, hmdeath⟩ := hs.lift_kernel gradeA_le_gradeB (kanHookVector k) hdie
  refine ⟨m, hm, ?_, hmdeath⟩
  intro hm0
  have hz : kanHookVector k = 0 := by
    rw [← hm, hm0, map_zero]
  have hsource := congrArg
    (fun x => (planarGrid.appIso (finiteHook k) gradeA gradeA_hasLowerPoint).hom.hom x) hz
  have hvec : floorHookVector k gradeA gradeA_hasLowerPoint = 0 := by
    simpa [kanHookVector] using hsource
  exact floorHookVectorA_ne_zero k hvec

/-- The same actual quotient and nonzero dying lift work over characteristic two. -/
theorem characteristic_two_nonzero_dying_lift :
    ∃ m : (planarGrid.lan.obj (FiniteHookDeflation.module (finiteHook (ZMod 2)))).obj gradeA,
      ((planarGrid.lan.map (FiniteHookDeflation.π (finiteHook (ZMod 2)))).app gradeA).hom m =
          kanHookVector (ZMod 2) ∧
        m ≠ 0 ∧
        structureMapLinear
          (planarGrid.lan.obj (FiniteHookDeflation.module (finiteHook (ZMod 2))))
          gradeA_le_gradeB m = 0 :=
  rankExact_lifts_nonzero_dying_vector (ZMod 2)

noncomputable def emptyGrid : CoordinateGrid 2 := by
  classical
  exact fun _ => ∅

private theorem emptyGrid_no_lowerPoint (a : Fin 2 → ℝ) :
    ¬ emptyGrid.HasLowerPoint a := by
  rintro ⟨p, _⟩
  have hp : (p 0).val ∈ (∅ : Finset ℝ) := by
    simpa [emptyGrid] using (p 0).property
  simp at hp

/-- An empty coordinate grid gives an actual zero Lan fiber at every real grade. -/
theorem empty_grid_lan_fiber_isZero (a : Fin 2 → ℝ) :
    IsZero ((emptyGrid.lan.obj (0 : PModule ℚ emptyGrid.Point)).obj a) :=
  emptyGrid.isZero_obj_of_not_hasLowerPoint _ a (emptyGrid_no_lowerPoint a)

noncomputable def negativeGrade : Fin 2 → ℝ := fun _ => -1

private theorem negativeGrade_no_lowerPoint :
    ¬ planarGrid.HasLowerPoint negativeGrade := by
  rintro ⟨p, hp⟩
  have hp0 := hp 0
  change (p 0).val ≤ -1 at hp0
  rcases planar_mem p 0 with h | h
  · rw [h] at hp0
    norm_num at hp0
  · rw [h] at hp0
    norm_num at hp0

/-- Grades below the least grid point have an actual zero Lan fiber. -/
theorem below_minimum_lan_fiber_isZero :
    IsZero ((planarGrid.lan.obj (finiteHook ℚ)).obj negativeGrade) :=
  planarGrid.isZero_obj_of_not_hasLowerPoint _ negativeGrade negativeGrade_no_lowerPoint

private theorem zeroInput_lan_fiber_eq_zero (a : Fin 2 → ℝ)
    (x : (planarGrid.lan.obj (0 : PModule ℚ planarGrid.Point)).obj a) : x = 0 := by
  by_cases ha : planarGrid.HasLowerPoint a
  · let e := (planarGrid.appIso (0 : PModule ℚ planarGrid.Point) a ha).toLinearEquiv
    apply e.injective
    change e x = e 0
    rw [map_zero]
    exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj _)).elim _ _
  · exact planarGrid.eq_zero_of_not_hasLowerPoint _ a ha x

/-- The zero input module remains zero in every actual Kan fiber. -/
theorem zero_input_lan_fiber_isZero (a : Fin 2 → ℝ) :
    IsZero ((planarGrid.lan.obj (0 : PModule ℚ planarGrid.Point)).obj a) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact zeroInput_lan_fiber_eq_zero a x

noncomputable def zeroGrid : CoordinateGrid 0 := fun i => Fin.elim0 i

noncomputable def zeroGridPoint : zeroGrid.Point := fun i => Fin.elim0 i

noncomputable def zeroGridGrade : Fin 0 → ℝ := fun i => Fin.elim0 i

noncomputable abbrev zeroDimPrincipalUpset : PModule ℚ zeroGrid.Point :=
  HookInfinity.module zeroGridPoint

private instance zeroDimPrincipalUpset_finiteDimensional (p : zeroGrid.Point) :
    FiniteDimensional ℚ (zeroDimPrincipalUpset.obj p) := by
  have hp : p = zeroGridPoint := by
    funext i
    exact Fin.elim0 i
  subst p
  infer_instance

private theorem zeroGrid_hasLowerPoint : zeroGrid.HasLowerPoint zeroGridGrade := by
  refine ⟨zeroGridPoint, ?_⟩
  intro i
  exact Fin.elim0 i

private theorem zeroGrid_floor :
    zeroGrid.floor zeroGridGrade zeroGrid_hasLowerPoint = zeroGridPoint := by
  apply (zeroGrid.floor_eq_iff zeroGridGrade zeroGrid_hasLowerPoint zeroGridPoint).2
  constructor
  · intro i
    exact Fin.elim0 i
  · intro q _ i
    exact Fin.elim0 i

private theorem zeroDim_identity_rankExact :
    IsRankExact (𝟙 zeroDimPrincipalUpset) (0 : zeroDimPrincipalUpset ⟶ 0) := by
  have hshort : IsPointwiseShortExact (𝟙 zeroDimPrincipalUpset)
      (0 : zeroDimPrincipalUpset ⟶ 0) := by
    constructor
    · intro p x y h
      simpa using h
    · intro p x
      refine ⟨0, ?_⟩
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p
      ext x
      simp
  exact hshort.rankExact_of_section (0 : 0 ⟶ zeroDimPrincipalUpset) (by simp)

/-- The one-point zero-dimensional grid carries the identity rank-exact sequence after Lan. -/
theorem zero_dim_identity_lan_rankExact :
    IsRankExact (zeroGrid.lan.map (𝟙 zeroDimPrincipalUpset))
      (zeroGrid.lan.map (0 : zeroDimPrincipalUpset ⟶ 0)) :=
  zeroGrid.lan_isRankExact zeroDim_identity_rankExact

/-- The principal upset stays nonzero in the actual Lan fiber when n=0. -/
theorem zero_dim_principal_upset_lan_nonzero :
    ∃ x : (zeroGrid.lan.obj zeroDimPrincipalUpset).obj zeroGridGrade, x ≠ 0 := by
  let ha := zeroGrid_hasLowerPoint
  let p := zeroGrid.floor zeroGridGrade ha
  have hp : zeroGridPoint ≤ p := by
    have heq : zeroGridPoint = p := by
      change zeroGridPoint = zeroGrid.floor zeroGridGrade zeroGrid_hasLowerPoint
      exact zeroGrid_floor.symm
    exact heq ▸ le_rfl
  let e := HookInfinity.fiberEquivOfLe (R := ℚ) hp
  let v := e.symm 1
  let x := (zeroGrid.appIso zeroDimPrincipalUpset zeroGridGrade ha).inv.hom v
  refine ⟨x, ?_⟩
  intro hx
  have h := congrArg
    (fun y => (zeroGrid.appIso zeroDimPrincipalUpset zeroGridGrade ha).hom.hom y) hx
  have hv : v = 0 := by
    simpa [x] using h
  have hone : (1 : ℚ) = 0 := by
    have he := congrArg e hv
    simp [v] at he
  exact one_ne_zero hone

/-- The all-tail comparison uses the principal-upset fiber and actual Kan inverse. -/
theorem principal_upset_unbounded_tail (r : Fin 2 → ℝ) (hr : ∀ i, 2 ≤ r i) :
    ∃ x : (planarGrid.lan.obj
      (HookInfinity.module (R := ℚ) planarLower)).obj r, x ≠ 0 := by
  let ha : planarGrid.HasLowerPoint r := by
    refine ⟨planarUpper, ?_⟩
    intro i
    change (2 : ℝ) ≤ r i
    exact hr i
  let p := planarGrid.floor r ha
  have hbirth : planarLower ≤ p := planarLower_le p
  let e := HookInfinity.fiberEquivOfLe (R := ℚ) hbirth
  let v := e.symm 1
  let x := (planarGrid.appIso (HookInfinity.module (R := ℚ) planarLower) r ha).inv.hom v
  refine ⟨x, ?_⟩
  intro hx
  have hv : v = 0 := by
    have h := congrArg (fun y => (planarGrid.appIso
      (HookInfinity.module (R := ℚ) planarLower) r ha).hom.hom y) hx
    simpa [x] using h
  have hone : (1 : ℚ) = 0 := by
    have h := congrArg e hv
    simp [v] at h
  exact one_ne_zero hone

end TDA.Persistence.CoordinateGridKan.Examples
