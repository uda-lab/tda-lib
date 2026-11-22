import TDA.Persistence.Morse.FilteredContraction
import TDA.Persistence.Morse.UnitCancellationExamples

/-!
# Fixtures for filtered contractions

Evaluations of `TDA.Persistence.Morse.Cancellation.FilteredContraction` over `ZMod 2`, on the
filled triangle of `TDA.Persistence.Morse.UnitCancellationExamples` (positions 0–6 for A, B,
C, AB, BC, CA, ABC, with boundary `tD`).

* G1. With the grade `cGrade` (A, B, C, AB, BC at 0, CA at 1, ABC at 2), `step1` cancels
  (B, AB) and `step2` cancels (C, BC) on the survivors of step 1, giving the nested subtype
  `TS2`. The regrading is needed: with the list grades of `triangle`, no equal-grade unit pair
  remains after cancelling (B, AB). The composite `twoStep = step1.trans step2` has the single
  differential entry `d'' ABC = CA`; its projection sends A, B, C to A, CA to CA, ABC to ABC
  and AB, BC to 0; its inclusion sends A to A, CA to AB + BC + CA and ABC to ABC; its homotopy
  sends B to AB, C to AB + BC and every other generator to 0. All of the homotopy on C comes
  from the correction term `incl₁ * htpy₂ * proj₁`. `twoStep_values_homotopy` checks
  `1 - i p = D h + h D` on the written-out matrices directly.
* G2. `critEquiv` identifies `TS2` with the flat subtype `Crit` of the critical cells A, CA,
  ABC, and `critContraction = twoStep.reindex critEquiv` carries the same values, with the
  original grades. `critFlat` restates it by `copy` with the flat degree, grade and the
  differential `critD`.

Every closed computation is a kernel `decide`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.FilteredContractionExamples

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation
open TDA.Persistence.Morse.UnitCancellationExamples

/-! ## G1. Two cancellations on the filled triangle -/

/-- A, B, C, AB, BC at grade 0, CA at grade 1, ABC at grade 2. -/
def cGrade : T → ℤ := fun i => if i.val ≤ 4 then 0 else (i.val : ℤ) - 4

/-- `tD` is a filtered differential for `cGrade`. -/
theorem cGrade_isFilteredDifferential : IsFilteredDifferential tDegree cGrade tD :=
  ⟨triangle_isFilteredDifferential.toIsBasedDifferential, by decide +kernel⟩

/-- B and AB have grade 0. -/
theorem step1_grade_eq : cGrade tB = cGrade tAB := by decide +kernel

/-- Step 1: cancel (B, AB). -/
def step1 : FilteredContraction tDegree cGrade tD (tDegree ∘ Subtype.val)
    (cGrade ∘ Subtype.val) (reducedDifferential tD tB tAB) :=
  FilteredContraction.ofUnitPair cGrade_isFilteredDifferential triangle_isUnitPair step1_grade_eq

/-- (C, BC) is a unit pair of the first reduced differential. -/
theorem step2_isUnitPair : IsUnitPair (reducedDifferential tD tB tAB) sC sBC :=
  ⟨by decide, by decide +kernel⟩

/-- C and BC have grade 0. -/
theorem step2_grade_eq : (cGrade ∘ Subtype.val) sC = (cGrade ∘ Subtype.val) sBC := by
  decide +kernel

/-- The survivors of both cancellations, a nested subtype of `T`. -/
abbrev TS2 := PairSurvivor sC sBC

/-- Step 2: cancel (C, BC) in the survivors of step 1. -/
def step2 : FilteredContraction (tDegree ∘ Subtype.val) (cGrade ∘ Subtype.val)
    (reducedDifferential tD tB tAB) ((tDegree ∘ Subtype.val) ∘ Subtype.val)
    ((cGrade ∘ Subtype.val) ∘ Subtype.val)
    (reducedDifferential (reducedDifferential tD tB tAB) sC sBC) :=
  FilteredContraction.ofUnitPair
    (isFilteredDifferential_reduced cGrade_isFilteredDifferential triangle_isUnitPair
      step1_grade_eq)
    step2_isUnitPair step2_grade_eq

/-- The composite of the two steps. -/
def twoStep := step1.trans step2

/-- The final survivor A. -/
def uA : TS2 := ⟨sA, by decide⟩
/-- The final survivor CA. -/
def uCA : TS2 := ⟨sCA, by decide⟩
/-- The final survivor ABC. -/
def uABC : TS2 := ⟨sABC, by decide⟩

/-- The Morse differential: only `d ABC = CA`. -/
def twoStepD : Matrix TS2 TS2 (ZMod 2) := fun r s => if r = uCA ∧ s = uABC then 1 else 0

/-- The second reduced differential is `twoStepD`. -/
theorem twoStep_differential :
    reducedDifferential (reducedDifferential tD tB tAB) sC sBC = twoStepD := by decide +kernel

/-- `p` sends A, B, C to A, CA to CA, ABC to ABC, and AB, BC to 0. -/
def twoStepProj : Matrix TS2 T (ZMod 2) := fun r x =>
  if (r = uA ∧ x.val ≤ 2) ∨ (r = uCA ∧ x = tCA) ∨ (r = uABC ∧ x = tABC) then 1 else 0

/-- The composed projection. -/
theorem twoStep_proj : twoStep.proj = twoStepProj := by decide +kernel

/-- `i` sends A to A, CA to AB + BC + CA, ABC to ABC. -/
def twoStepIncl : Matrix T TS2 (ZMod 2) := fun x r =>
  if (x = tA ∧ r = uA) ∨ ((x = tAB ∨ x = tBC ∨ x = tCA) ∧ r = uCA) ∨ (x = tABC ∧ r = uABC)
  then 1 else 0

/-- The composed inclusion. -/
theorem twoStep_incl : twoStep.incl = twoStepIncl := by decide +kernel

/-- `h` sends B to AB and C to AB + BC. -/
def twoStepHtpy : Matrix T T (ZMod 2) := fun x y =>
  if (x = tAB ∧ (y = tB ∨ y = tC)) ∨ (x = tBC ∧ y = tC) then 1 else 0

/-- The composed homotopy `h₁ + i₁ h₂ p₁`. -/
theorem twoStep_htpy : twoStep.htpy = twoStepHtpy := by decide +kernel

/-- The written-out matrices satisfy the homotopy identity, evaluated directly. -/
theorem twoStep_values_homotopy :
    1 - twoStepIncl * twoStepProj = tD * twoStepHtpy + twoStepHtpy * tD := by decide +kernel

/-! ## G2. Transport to the critical cells -/

/-- The critical cells A, CA, ABC as a Finset of original positions. -/
def critSet : Finset T := {tA, tCA, tABC}

/-- The critical cells as a subtype of the original positions. -/
abbrev Crit := {x : T // x ∈ critSet}

/-- Membership in `critSet` is survival of both cancellations. -/
theorem mem_critSet_iff (x : T) :
    x ∈ critSet ↔ (x ≠ tB ∧ x ≠ tAB) ∧ (x ≠ tC ∧ x ≠ tBC) := by
  revert x; decide +kernel

/-- Forget the nesting. -/
def critEquiv : TS2 ≃ Crit where
  toFun u := ⟨u.val.val, (mem_critSet_iff _).mpr ⟨u.val.property, by
    exact ⟨fun h => u.property.1 (Subtype.ext h), fun h => u.property.2 (Subtype.ext h)⟩⟩⟩
  invFun x := ⟨⟨x.val, ((mem_critSet_iff _).mp x.property).1⟩, by
    have h := ((mem_critSet_iff _).mp x.property).2
    exact ⟨fun e => h.1 (congrArg Subtype.val e), fun e => h.2 (congrArg Subtype.val e)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The composite contraction transported to `Crit`. -/
def critContraction := twoStep.reindex critEquiv

/-- The critical cell A. -/
def cA : Crit := ⟨tA, by decide⟩
/-- The critical cell CA. -/
def cCA : Crit := ⟨tCA, by decide⟩
/-- The critical cell ABC. -/
def cABC : Crit := ⟨tABC, by decide⟩

/-- The Morse differential on `Crit`: only `d ABC = CA`. -/
def critD : Matrix Crit Crit (ZMod 2) := fun r s => if r = cCA ∧ s = cABC then 1 else 0

/-- The transported differential is `critD`. -/
theorem crit_differential :
    (reducedDifferential (reducedDifferential tD tB tAB) sC sBC).submatrix critEquiv.symm
      critEquiv.symm = critD := by decide +kernel

/-- The transported projection, written out. -/
def critProj : Matrix Crit T (ZMod 2) := fun r x =>
  if (r = cA ∧ x.val ≤ 2) ∨ (r = cCA ∧ x = tCA) ∨ (r = cABC ∧ x = tABC) then 1 else 0

/-- The transported projection is `critProj`. -/
theorem crit_proj : critContraction.proj = critProj := by decide +kernel

/-- The transported inclusion, written out. -/
def critIncl : Matrix T Crit (ZMod 2) := fun x r =>
  if (x = tA ∧ r = cA) ∨ ((x = tAB ∨ x = tBC ∨ x = tCA) ∧ r = cCA) ∨ (x = tABC ∧ r = cABC)
  then 1 else 0

/-- The transported inclusion is `critIncl`. -/
theorem crit_incl : critContraction.incl = critIncl := by decide +kernel

/-- Transport keeps the composed homotopy. -/
theorem crit_htpy : critContraction.htpy = twoStepHtpy := by decide +kernel

/-- The transported grades are the original grades. -/
theorem crit_grade :
    ∀ r : Crit, ((cGrade ∘ Subtype.val) ∘ Subtype.val) (critEquiv.symm r) = cGrade r.val := by
  decide +kernel

/-- The transported contraction restated on `Crit` with the flat degree, grade and
differential, by `copy`. -/
def critFlat : FilteredContraction tDegree cGrade tD (tDegree ∘ Subtype.val)
    (cGrade ∘ Subtype.val) critD :=
  critContraction.copy (funext fun _ => rfl) (funext fun _ => rfl) crit_differential

/-- `copy` keeps the transported projection. -/
theorem critFlat_proj : critFlat.proj = critProj := by decide +kernel

/-- `copy` keeps the transported inclusion. -/
theorem critFlat_incl : critFlat.incl = critIncl := by decide +kernel

end TDA.Persistence.Morse.FilteredContractionExamples
