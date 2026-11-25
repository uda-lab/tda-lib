import TDA.Persistence.Morse.UnitCancellation

/-!
# Fixtures for one equal-grade unit cancellation

Evaluations of `TDA.Persistence.Morse.Cancellation` over `ZMod 2`.

* The filled triangle (`triangle`, positions 0–6 for A, B, C, AB, BC, CA, ABC) with A, B, C,
  AB at grade 0, BC, CA at grade 1 and ABC at grade 2. Cancelling the equal-grade pair
  (B, AB) changes `d BC = B + C` into `d' BC = A + C` and leaves `d' ABC = BC + CA`; `B` is
  also a face of `BC`, so it is not a free face of `AB` at the final level.
* The pure unit pair `d b = a` on `Fin 2`, where `H` is a contracting homotopy of the whole
  complex and no generator survives.
* The same complex with `a` at grade 0 and `b` at grade 1. Its grade-0 sublevel is the cycle
  `a`, which is not a boundary there, and `a` becomes the boundary of `b` at grade 1, so the
  barcode has the bar `[0, 1)`; this is an explanation only, since no homology or barcode is
  formalised here. `H` raises grade, and no grade-nonincreasing `H` satisfies
  `1 - i p = D H + H D` for any `p` and `i` onto the empty survivor complex.
* A tie-order example on `Fin 4` at a single grade, where the reduced differential has a
  nonzero entry `d' s = r` with `s` listed before `r`, so the inherited order is not
  triangular after cancellation.

* A signed instance over `ℤ` (`zD`, positions 0–6 for A, B, C, AB, BC, AC, ABC, with
  `∂AB = B - A`, `∂BC = C - B`, `∂AC = C - A`, `∂ABC = BC - AC + AB`). The reduced differential
  of (B, AB) has the entry `d' BC = C - A` with `-1` at A, the projection of (BC, ABC) has the
  entries `-1` at AB and `+1` at AC, and the inclusion of (C, AC) has the entry `-1`; all are
  written by hand, and the homotopy identity `1 - i p = D H + H D` is evaluated directly. A
  negative control, the pair (A, AB) with incidence `-1`, is not a unit pair, its entry formulas
  are not square-zero and the homotopy identity fails.

Every closed computation is a kernel `decide`. `triangle_boundary` first unfolds the boundary
with `norm_num`, and `unequal_no_filtered_contraction` quantifies over all matrices.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.UnitCancellationExamples

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation

/-! ## F1. Filled triangle -/

/-- The filled triangle: A, B, C, AB at grade 0, BC, CA at grade 1, ABC at grade 2. -/
def triangle : FiniteInput.Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 0), ({1, 2}, 1), ({0, 2}, 1), ({0, 1, 2}, 2)]

/-- `triangle` is a valid finite input. -/
theorem triangle_valid : FiniteInput.Valid triangle :=
  (FiniteInput.validBool_iff _).mp (by decide +kernel)

/-- The positions of `triangle`. -/
abbrev T := Fin triangle.length

/-- The list grade of each position of `triangle`. -/
def tGrade : T → ℤ := fun i => (triangle.get i).2

/-- The homological degree of each position of `triangle`. -/
def tDegree : T → ℕ := FiniteInput.degree triangle

/-- The boundary of `triangle`, written out. -/
def tD : Matrix T T (ZMod 2) := fun r c =>
  if c.val = 3 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
  else if c.val = 4 then (if r.val = 1 ∨ r.val = 2 then 1 else 0)
  else if c.val = 5 then (if r.val = 0 ∨ r.val = 2 then 1 else 0)
  else if c.val = 6 then (if r.val = 3 ∨ r.val = 4 ∨ r.val = 5 then 1 else 0)
  else 0

/-- `tD` is the finite-input boundary of `triangle`. -/
theorem triangle_boundary : FiniteInput.boundary triangle = tD := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FiniteInput.boundary, triangle, tD, Finset.orderEmbOfFin_apply,
      Finset.sort_insert, Finset.sort_singleton] <;> decide +kernel

/-- `tD` is a filtered differential for the degrees and list grades of `triangle`. -/
theorem triangle_isFilteredDifferential : IsFilteredDifferential tDegree tGrade tD :=
  triangle_boundary ▸ isFilteredDifferential_boundary triangle triangle_valid

/-- Position 0, the vertex A. -/
def tA : T := ⟨0, by decide⟩
/-- Position 1, the vertex B. -/
def tB : T := ⟨1, by decide⟩
/-- Position 2, the vertex C. -/
def tC : T := ⟨2, by decide⟩
/-- Position 3, the edge AB. -/
def tAB : T := ⟨3, by decide⟩
/-- Position 4, the edge BC. -/
def tBC : T := ⟨4, by decide⟩
/-- Position 5, the edge CA. -/
def tCA : T := ⟨5, by decide⟩
/-- Position 6, the face ABC. -/
def tABC : T := ⟨6, by decide⟩

/-- The survivors of cancelling (B, AB). -/
abbrev TS := PairSurvivor tB tAB

/-- The survivor A. -/
def sA : TS := ⟨tA, by decide⟩
/-- The survivor C. -/
def sC : TS := ⟨tC, by decide⟩
/-- The survivor BC. -/
def sBC : TS := ⟨tBC, by decide⟩
/-- The survivor CA. -/
def sCA : TS := ⟨tCA, by decide⟩
/-- The survivor ABC. -/
def sABC : TS := ⟨tABC, by decide⟩

/-- (B, AB) is a unit pair of `tD`. -/
theorem triangle_isUnitPair : IsUnitPair tD tB tAB := ⟨by decide, by decide +kernel⟩

/-- B and AB both have grade 0. -/
theorem triangle_grade_eq : tGrade tB = tGrade tAB := by decide +kernel

/-- `B` is not a free face of `AB` at the final level: it is also a face of `BC`. -/
theorem triangle_not_free : tD tB tBC = 1 := by decide +kernel

/-- `d' BC = A + C`. -/
theorem triangle_reduced_BC :
    ∀ r : TS, reducedDifferential tD tB tAB r sBC = if r = sA ∨ r = sC then 1 else 0 := by
  decide +kernel

/-- `d' ABC = BC + CA`, unchanged. -/
theorem triangle_reduced_ABC :
    ∀ r : TS, reducedDifferential tD tB tAB r sABC = if r = sBC ∨ r = sCA then 1 else 0 := by
  decide +kernel

/-- The matrix correction is nonzero: `A` is not a face of `BC` originally. -/
theorem triangle_correction : tD tA tBC = 0 ∧ reducedDifferential tD tB tAB sA sBC = 1 := by
  decide +kernel

/-- The whole reduced differential: `d' BC = d' CA = A + C`, `d' ABC = BC + CA`. -/
def tReduced : Matrix TS TS (ZMod 2) := fun r s =>
  if ((r = sA ∨ r = sC) ∧ (s = sBC ∨ s = sCA)) ∨ ((r = sBC ∨ r = sCA) ∧ s = sABC) then 1 else 0

/-- The reduced differential of (B, AB) is `tReduced`. -/
theorem triangle_reduced : reducedDifferential tD tB tAB = tReduced := by decide +kernel

/-! ## F2. Pure unit pair -/

/-- The two-cell complex `d b = a`, with `a = 0` and `b = 1`. -/
def uD : Matrix (Fin 2) (Fin 2) (ZMod 2) := fun r c => if r = 0 ∧ c = 1 then 1 else 0

/-- Degree 0 for `a`, degree 1 for `b`. -/
def uDegree : Fin 2 → ℕ := fun i => i.val

/-- Both generators at grade 0. -/
def uGrade : Fin 2 → ℤ := fun _ => 0

/-- `uD` is a filtered differential for `uDegree` and `uGrade`. -/
theorem unit_isFilteredDifferential : IsFilteredDifferential uDegree uGrade uD :=
  ⟨⟨by decide +kernel, fun r c => by fin_cases r <;> fin_cases c <;> decide +kernel⟩,
    by decide +kernel⟩

/-- (0, 1) is a unit pair of `uD`. -/
theorem unit_isUnitPair : IsUnitPair uD 0 1 := ⟨by decide, by decide +kernel⟩

/-- No generator survives. -/
theorem unit_survivor_card : Fintype.card (PairSurvivor (0 : Fin 2) 1) = 0 := by decide +kernel

/-- `H` is a contracting homotopy of the whole complex, evaluated directly. -/
theorem unit_contraction :
    (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) = uD * homotopy 0 1 + homotopy 0 1 * uD := by
  decide +kernel

/-! ## F3. Unequal grades -/

/-- `a` at grade 0 and `b` at grade 1. -/
def vGrade : Fin 2 → ℤ := fun i => (i.val : ℤ)

/-- `uD` is still a filtered differential with the unequal grades `vGrade`. -/
theorem unequal_isFilteredDifferential : IsFilteredDifferential uDegree vGrade uD :=
  ⟨unit_isFilteredDifferential.toIsBasedDifferential, by decide +kernel⟩

/-- With unequal grades, `H a = b` raises grade. -/
theorem unequal_homotopy_not_filtered :
    ¬ GradeNonincreasing vGrade vGrade
      (homotopy (0 : Fin 2) 1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  decide +kernel

/-- No grade-nonincreasing homotopy contracts onto the (empty) survivor complex,
whatever `p` and `i` are. -/
theorem unequal_no_filtered_contraction :
    ¬ ∃ (p : Matrix (PairSurvivor (0 : Fin 2) 1) (Fin 2) (ZMod 2))
        (i : Matrix (Fin 2) (PairSurvivor (0 : Fin 2) 1) (ZMod 2))
        (H : Matrix (Fin 2) (Fin 2) (ZMod 2)),
      GradeNonincreasing vGrade vGrade H ∧ 1 - i * p = uD * H + H * uD := by
  rintro ⟨p, i, H, hH, heq⟩
  have : IsEmpty (PairSurvivor (0 : Fin 2) 1) :=
    ⟨fun ⟨x, hx⟩ => by fin_cases x <;> simp at hx⟩
  have hip : i * p = 0 := by
    ext x y
    simp [Matrix.mul_apply]
  have hH10 : H 1 0 = 0 := by
    by_contra hne
    have := hH 1 0 hne
    simp [vGrade] at this
  have h00 := congrFun (congrFun heq 0) 0
  rw [hip, sub_zero] at h00
  simp [Matrix.add_apply, Matrix.mul_apply, uD, hH10] at h00

/-! ## F4. Tie order -/

/-- At one grade, `a < s < r < b` with `d s = a` and `d b = a + r` (`a, s, r, b = 0, 1, 2, 3`). -/
def wD : Matrix (Fin 4) (Fin 4) (ZMod 2) := fun r c =>
  if (r = 0 ∧ c = 1) ∨ (r = 0 ∧ c = 3) ∨ (r = 2 ∧ c = 3) then 1 else 0

/-- `a`, `r` in degree 0 and `s`, `b` in degree 1. -/
def wDegree : Fin 4 → ℕ := fun i => i.val % 2

/-- Every generator at grade 0. -/
def wGrade : Fin 4 → ℤ := fun _ => 0

/-- `wD` is a filtered differential for `wDegree` and `wGrade`. -/
theorem tie_isFilteredDifferential : IsFilteredDifferential wDegree wGrade wD :=
  ⟨⟨by decide +kernel, fun r c => by fin_cases r <;> fin_cases c <;> decide +kernel⟩,
    by decide +kernel⟩

/-- (a, b) = (0, 3) is a unit pair of `wD`. -/
theorem tie_isUnitPair : IsUnitPair wD 0 3 := ⟨by decide, by decide +kernel⟩

/-- The survivor `s`, at position 1. -/
def wS : PairSurvivor (0 : Fin 4) 3 := ⟨1, by decide⟩

/-- The survivor `r`, at position 2. -/
def wR : PairSurvivor (0 : Fin 4) 3 := ⟨2, by decide⟩

/-- The reduced differential `d' s = r`, written out. -/
def wReduced : Matrix (PairSurvivor (0 : Fin 4) 3) (PairSurvivor (0 : Fin 4) 3) (ZMod 2) :=
  fun r s => if r = wR ∧ s = wS then 1 else 0

/-- The reduced differential of (a, b) is `wReduced`. -/
theorem tie_reduced : reducedDifferential wD 0 3 = wReduced := by decide +kernel

/-- `d' s = r` is a new entry although `s` precedes `r`. -/
theorem tie_not_triangular :
    wD wR.val wS.val = 0 ∧ reducedDifferential wD 0 3 wR wS = 1 ∧ wS.val < wR.val := by
  decide +kernel

/-! ## F5. A signed instance over `ℤ` -/

/-- The filled triangle over `ℤ` with the usual signed boundary, on positions 0–6 for A, B, C,
AB, BC, AC, ABC: `∂AB = B - A`, `∂BC = C - B`, `∂AC = C - A`, `∂ABC = BC - AC + AB`. The
entries `-1` make a wrong sign in `projection`, `inclusion` or `reducedDifferential` visible,
which no fixture over `ZMod 2` can do. -/
def zD : Matrix (Fin 7) (Fin 7) ℤ := fun r c =>
  if c = 3 then (if r = 0 then -1 else if r = 1 then 1 else 0)
  else if c = 4 then (if r = 1 then -1 else if r = 2 then 1 else 0)
  else if c = 5 then (if r = 0 then -1 else if r = 2 then 1 else 0)
  else if c = 6 then (if r = 4 then 1 else if r = 5 then -1 else if r = 3 then 1 else 0)
  else 0

/-- `zD` squares to zero over `ℤ`. -/
theorem zD_sq : zD * zD = 0 := by decide +kernel

/-- (B, AB) has coefficient `+1`: a unit pair. -/
theorem zD_unitPair : IsUnitPair zD 1 3 := ⟨by decide, by decide +kernel⟩

/-- Expected values, written by hand, of the reduced differential of (B, AB):
`d' BC = C - A`, with the entry `-1` at A, and `d' ABC = BC - AC`, since AB is cancelled. -/
theorem zD_reduced_values :
    (∀ r : PairSurvivor (1 : Fin 7) 3, reducedDifferential zD 1 3 r ⟨4, by decide⟩ =
      if r.val = 0 then -1 else if r.val = 2 then 1 else 0) ∧
    (∀ r : PairSurvivor (1 : Fin 7) 3, reducedDifferential zD 1 3 r ⟨6, by decide⟩ =
      if r.val = 4 then 1 else if r.val = 5 then -1 else 0) := by
  constructor <;> decide +kernel

/-- (BC, ABC) has coefficient `+1`: a unit pair. -/
theorem zD_unitPair_BC_ABC : IsUnitPair zD 4 6 := ⟨by decide, by decide +kernel⟩

/-- Expected values of the projection of (BC, ABC) on the generator BC:
`p (AB) = -∂ABC_{AB} = -1` and `p (AC) = +1`, the projection of the coefficient
`-D s ABC`. -/
theorem zD_projection_values :
    ∀ s : PairSurvivor (4 : Fin 7) 6, projection zD 4 6 s 4 =
      if s.val = 3 then -1 else if s.val = 5 then 1 else 0 := by
  decide +kernel

/-- (C, AC) has coefficient `+1`: a unit pair. -/
theorem zD_unitPair_C_AC : IsUnitPair zD 2 5 := ⟨by decide, by decide +kernel⟩

/-- Expected values of the inclusion of (C, AC) on the coefficient of `AC`: the survivor BC goes
to `BC - D[C, BC] AC = BC - AC`, with the entry `-1` at AC. -/
theorem zD_inclusion_values :
    ∀ s : PairSurvivor (2 : Fin 7) 5, inclusion zD 2 5 5 s = if s.val = 4 then -1 else 0 := by
  decide +kernel

/-- The homotopy identity `1 - i p = D H + H D` for (B, AB), evaluated directly over `ℤ`,
independently of the general proof. -/
theorem zD_homotopy_identity :
    1 - inclusion zD 1 3 * projection zD 1 3 = zD * homotopy 1 3 + homotopy 1 3 * zD := by
  decide +kernel

/-- The homotopy identity for (C, AC), evaluated directly over `ℤ`. -/
theorem zD_homotopy_identity_C_AC :
    1 - inclusion zD 2 5 * projection zD 2 5 = zD * homotopy 2 5 + homotopy 2 5 * zD := by
  decide +kernel

/-! ## F6. Negative control: incidence `-1` -/

/-- (A, AB) has coefficient `-1`, which is a unit of `ℤ` but not `1`, so it is not an
`IsUnitPair` over `ℤ` (over `ZMod 2` it is, since `-1 = 1` there). -/
theorem zD_not_unitPair_A_AB : ¬ IsUnitPair zD 0 3 :=
  fun h => absurd h.coeff (by decide +kernel)

/-- What fails for the pair (A, AB) if the entry formulas are used regardless: the reduced
differential is not square-zero. -/
theorem zD_negative_reduced_sq_ne_zero :
    reducedDifferential zD 0 3 * reducedDifferential zD 0 3 ≠ 0 := by decide +kernel

/-- … and the homotopy identity fails as well. -/
theorem zD_negative_homotopy_identity_fails :
    1 - inclusion zD 0 3 * projection zD 0 3 ≠ zD * homotopy 0 3 + homotopy 0 3 * zD := by
  decide +kernel

end TDA.Persistence.Morse.UnitCancellationExamples
