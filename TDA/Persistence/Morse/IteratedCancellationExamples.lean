import TDA.Persistence.Morse.IteratedCancellation
import TDA.Persistence.Morse.FilteredContractionExamples
import TDA.Persistence.Morse.FiniteInputMatchingExamples

/-!
# Fixtures for iterated cancellation

Evaluations of `TDA.Persistence.Morse.Cancellation.FilteredContraction.ofSchedule` over
`ZMod 2`.

* H1. The multi-grade square `square` of `TDA.Persistence.Morse.FiniteInputMatchingExamples`
  (positions 0–10 for A, B, C, D, AB, BC, CD, AD, AC, ABC, ACD; A–CD at grade 0, AD at 1,
  AC, ABC, ACD at 2) with the certified pairs of `squarePairs`, scheduled in increasing rank of
  the lower face for the rank of `square_check`: (AC, ABC), (D, CD), (C, BC), (B, AB). On
  `FiniteInput.boundary square` this is a pivot schedule, and the list order of `squarePairs`
  is not. The critical positions are A, AD, ACD, the reduced differential has the single entry
  `d ACD = AD`, and the projection, inclusion and homotopy are written out.
* H2. The regraded filled triangle of `TDA.Persistence.Morse.FilteredContractionExamples` with
  the schedule (C, BC), (B, AB). The reduced differential, projection, inclusion and homotopy
  agree with G1 and G2. G1 cancels the same pairs in the opposite order, which is not a pivot
  schedule: the invariant is sufficient for the recursion, not necessary.
* N. The hollow triangle `circle` with the cyclic pairs (A, AB), (B, BC), (C, AC) of
  `cyclicPairs`. None of the six orders is a pivot schedule, and cancelling (A, AB) and then
  (B, BC) leaves coefficient 0 at (C, AC).

Every closed computation is a kernel `decide`. `square_boundary` and `circle_boundary` first
unfold the boundary with `norm_num`, as `triangle_boundary` does.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.IteratedCancellationExamples

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation
open TDA.Persistence.Morse.UnitCancellationExamples
open TDA.Persistence.Morse.FilteredContractionExamples
open TDA.Persistence.Morse.FiniteInputMatchingExamples (square square_valid squarePairs circle
  circle_valid cyclicPairs)

/-! ## H1. The multi-grade square with diagonal -/

/-- The positions of `square`: A, B, C, D, AB, BC, CD at grade 0, AD at 1, AC, ABC, ACD at 2. -/
abbrev Sq := Fin square.length

/-- The list grade of each position of `square`. -/
def sqGrade : Sq → ℤ := fun i => (square.get i).2

/-- The homological degree of each position of `square`. -/
def sqDegree : Sq → ℕ := FiniteInput.degree square

/-- Position 0, the vertex A. -/
def qA : Sq := ⟨0, by decide⟩
/-- Position 1, the vertex B. -/
def qB : Sq := ⟨1, by decide⟩
/-- Position 2, the vertex C. -/
def qC : Sq := ⟨2, by decide⟩
/-- Position 3, the vertex D. -/
def qD : Sq := ⟨3, by decide⟩
/-- Position 4, the edge AB. -/
def qAB : Sq := ⟨4, by decide⟩
/-- Position 5, the edge BC. -/
def qBC : Sq := ⟨5, by decide⟩
/-- Position 6, the edge CD. -/
def qCD : Sq := ⟨6, by decide⟩
/-- Position 7, the edge AD. -/
def qAD : Sq := ⟨7, by decide⟩
/-- Position 8, the diagonal AC. -/
def qAC : Sq := ⟨8, by decide⟩
/-- Position 9, the triangle ABC. -/
def qABC : Sq := ⟨9, by decide⟩
/-- Position 10, the triangle ACD. -/
def qACD : Sq := ⟨10, by decide⟩

/-- The boundary of `square`, written out. -/
def sqD : Matrix Sq Sq (ZMod 2) := fun r c =>
  if c = qAB then (if r = qA ∨ r = qB then 1 else 0)
  else if c = qBC then (if r = qB ∨ r = qC then 1 else 0)
  else if c = qCD then (if r = qC ∨ r = qD then 1 else 0)
  else if c = qAD then (if r = qA ∨ r = qD then 1 else 0)
  else if c = qAC then (if r = qA ∨ r = qC then 1 else 0)
  else if c = qABC then (if r = qAB ∨ r = qBC ∨ r = qAC then 1 else 0)
  else if c = qACD then (if r = qCD ∨ r = qAD ∨ r = qAC then 1 else 0)
  else 0

/-- `sqD` is the finite-input boundary of `square`. -/
theorem square_boundary : FiniteInput.boundary square = sqD := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FiniteInput.boundary, square, sqD, qA, qB, qC, qD, qAB, qBC, qCD, qAD, qAC,
      qABC, qACD, Finset.orderEmbOfFin_apply, Finset.sort_insert, Finset.sort_singleton] <;>
    decide +kernel

/-- The boundary of `square` is a filtered differential for its degrees and list grades. -/
theorem square_isFilteredDifferential :
    IsFilteredDifferential sqDegree sqGrade (FiniteInput.boundary square) :=
  isFilteredDifferential_boundary square square_valid

/-- The pairs of `squarePairs` in increasing rank of the lower face for the certified rank of
`square_check`: (AC, ABC), (D, CD), (C, BC), (B, AB). -/
def sqSchedule : List (Sq × Sq) := [(qAC, qABC), (qD, qCD), (qC, qBC), (qB, qAB)]

/-- `sqSchedule` reorders the certified pairs. -/
theorem sqSchedule_perm : sqSchedule.Perm squarePairs := by decide +kernel

/-- `sqSchedule` satisfies the pivot invariant for the boundary of `square`. -/
theorem sqSchedule_isPivotSchedule :
    IsPivotSchedule sqGrade (FiniteInput.boundary square) sqSchedule := by
  rw [square_boundary]; decide +kernel

/-- The list order of `squarePairs` does not: B, the lower face of its first pair, is a face
of BC, the upper face of its second pair. -/
theorem squarePairs_not_isPivotSchedule :
    ¬ IsPivotSchedule sqGrade (FiniteInput.boundary square) squarePairs := by
  rw [square_boundary]; decide +kernel

/-- The schedule contraction of the square onto A, AD, ACD. -/
def sqContraction := FilteredContraction.ofSchedule square_isFilteredDifferential
  sqSchedule_isPivotSchedule

/-- The critical positions are A, AD and ACD. -/
theorem sq_criticalSet : criticalSet sqSchedule = {qA, qAD, qACD} := by decide +kernel

/-- The square's Morse differential on the critical positions: only `d ACD = AD`. -/
def sqCritD : Matrix (Critical sqSchedule) (Critical sqSchedule) (ZMod 2) := fun r s =>
  if r.val = qAD ∧ s.val = qACD then 1 else 0

/-- The reduced differential of the boundary of `square` is `sqCritD`. -/
theorem sq_criticalDifferential :
    criticalDifferential (FiniteInput.boundary square) sqSchedule = sqCritD := by
  rw [square_boundary]; decide +kernel

/-- `sqD` is a filtered differential for the degrees and list grades of `square`. -/
theorem sqD_isFilteredDifferential : IsFilteredDifferential sqDegree sqGrade sqD :=
  square_boundary ▸ square_isFilteredDifferential

/-- `sqSchedule` satisfies the pivot invariant for `sqD`. -/
theorem sqD_isPivotSchedule : IsPivotSchedule sqGrade sqD sqSchedule := by decide +kernel

/-- The projection sends A, B, C, D to A, AD to AD, ACD to ACD, and every other position
to 0. -/
def sqProj : Matrix (Critical sqSchedule) Sq (ZMod 2) := fun r x =>
  if (r.val = qA ∧ x.val ≤ 3) ∨ (r.val = qAD ∧ x = qAD) ∨ (r.val = qACD ∧ x = qACD)
  then 1 else 0

/-- The projection of `sqContraction` is `sqProj`. -/
theorem sq_proj : sqContraction.proj = sqProj := by
  rw [sqContraction, (FilteredContraction.ofSchedule_congr square_boundary _ _
    sqD_isFilteredDifferential sqD_isPivotSchedule).1]
  decide +kernel

/-- The inclusion sends A to A, AD to AB + BC + CD + AD, and ACD to ABC + ACD. -/
def sqIncl : Matrix Sq (Critical sqSchedule) (ZMod 2) := fun x r =>
  if (x = qA ∧ r.val = qA) ∨ ((x = qAB ∨ x = qBC ∨ x = qCD ∨ x = qAD) ∧ r.val = qAD) ∨
    ((x = qABC ∨ x = qACD) ∧ r.val = qACD) then 1 else 0

/-- The inclusion of `sqContraction` is `sqIncl`. -/
theorem sq_incl : sqContraction.incl = sqIncl := by
  rw [sqContraction, (FilteredContraction.ofSchedule_congr square_boundary _ _
    sqD_isFilteredDifferential sqD_isPivotSchedule).2.1]
  decide +kernel

/-- The homotopy sends B to AB, C to AB + BC, D to AB + BC + CD, AC to ABC, and every other
position to 0. -/
def sqHtpy : Matrix Sq Sq (ZMod 2) := fun x y =>
  if (x = qAB ∧ (y = qB ∨ y = qC ∨ y = qD)) ∨ (x = qBC ∧ (y = qC ∨ y = qD)) ∨
    (x = qCD ∧ y = qD) ∨ (x = qABC ∧ y = qAC) then 1 else 0

/-- The homotopy of `sqContraction` is `sqHtpy`. -/
theorem sq_htpy : sqContraction.htpy = sqHtpy := by
  rw [sqContraction, (FilteredContraction.ofSchedule_congr square_boundary _ _
    sqD_isFilteredDifferential sqD_isPivotSchedule).2.2]
  decide +kernel

/-! ## H2. The regraded triangle, compared with G1 and G2 -/

/-- (C, BC), then (B, AB): the G1 pairs in the order of the pivot invariant. -/
def triSchedule : List (T × T) := [(tC, tBC), (tB, tAB)]

/-- `triSchedule` satisfies the pivot invariant for `cGrade`. -/
theorem triSchedule_isPivotSchedule : IsPivotSchedule cGrade tD triSchedule := by
  decide +kernel

/-- G1's order (B, AB), (C, BC) does not, since B is a face of BC, although G1 cancels in that
order. -/
theorem g1Order_not_isPivotSchedule : ¬ IsPivotSchedule cGrade tD [(tB, tAB), (tC, tBC)] := by
  decide +kernel

/-- The schedule contraction of the regraded triangle. -/
def triContraction := FilteredContraction.ofSchedule cGrade_isFilteredDifferential
  triSchedule_isPivotSchedule

/-- The critical positions are those of `critSet`. -/
theorem tri_mem_criticalSet : ∀ x, x ∈ criticalSet triSchedule ↔ x ∈ critSet := by
  decide +kernel

/-- A critical position of `triSchedule` as an element of G2's `Crit`. -/
def toCrit (r : Critical triSchedule) : Crit := ⟨r.val, (tri_mem_criticalSet _).mp r.property⟩

/-- The reduced differential is G2's `critD`, read through `toCrit`. -/
theorem tri_criticalDifferential :
    criticalDifferential tD triSchedule = critD.submatrix toCrit toCrit := by
  decide +kernel

/-- The projection is G2's `critProj`, read through `toCrit`. -/
theorem tri_proj : triContraction.proj = critProj.submatrix toCrit id := by
  decide +kernel

/-- The inclusion is G2's `critIncl`, read through `toCrit`. -/
theorem tri_incl : triContraction.incl = critIncl.submatrix id toCrit := by
  decide +kernel

/-- The homotopy is G1's `twoStepHtpy`. -/
theorem tri_htpy : triContraction.htpy = twoStepHtpy := by decide +kernel

/-! ## N. A cyclic schedule destroys a later pivot -/

/-- The positions of `circle`: A, B, C, AB, BC, AC, all at grade 0. -/
abbrev Cir := Fin circle.length

/-- Position 0, the vertex A. -/
def oA : Cir := ⟨0, by decide⟩
/-- Position 1, the vertex B. -/
def oB : Cir := ⟨1, by decide⟩
/-- Position 2, the vertex C. -/
def oC : Cir := ⟨2, by decide⟩
/-- Position 3, the edge AB. -/
def oAB : Cir := ⟨3, by decide⟩
/-- Position 4, the edge BC. -/
def oBC : Cir := ⟨4, by decide⟩
/-- Position 5, the edge AC. -/
def oAC : Cir := ⟨5, by decide⟩

/-- The boundary of `circle`, written out. -/
def cirD : Matrix Cir Cir (ZMod 2) := fun r c =>
  if c = oAB then (if r = oA ∨ r = oB then 1 else 0)
  else if c = oBC then (if r = oB ∨ r = oC then 1 else 0)
  else if c = oAC then (if r = oA ∨ r = oC then 1 else 0)
  else 0

/-- `cirD` is the finite-input boundary of `circle`. -/
theorem circle_boundary : FiniteInput.boundary circle = cirD := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FiniteInput.boundary, circle, cirD, oA, oB, oC, oAB, oBC, oAC,
      Finset.orderEmbOfFin_apply, Finset.sort_insert, Finset.sort_singleton] <;>
    decide +kernel

/-- The six orders of the cyclic pairs (A, AB), (B, BC), (C, AC). -/
def cyclicOrders : List (List (Cir × Cir)) :=
  [[(oA, oAB), (oB, oBC), (oC, oAC)], [(oA, oAB), (oC, oAC), (oB, oBC)],
    [(oB, oBC), (oA, oAB), (oC, oAC)], [(oB, oBC), (oC, oAC), (oA, oAB)],
    [(oC, oAC), (oA, oAB), (oB, oBC)], [(oC, oAC), (oB, oBC), (oA, oAB)]]

/-- `cyclicOrders` lists six distinct reorderings of `cyclicPairs`. -/
theorem cyclicOrders_perm :
    cyclicOrders.Nodup ∧ cyclicOrders.length = 6 ∧
      ∀ l ∈ cyclicOrders, l.Perm cyclicPairs := by
  decide +kernel

/-- No order of the cyclic pairs is a pivot schedule. -/
theorem cyclic_not_isPivotSchedule : ∀ l ∈ cyclicOrders,
    ¬ IsPivotSchedule (fun i => (circle.get i).2) (FiniteInput.boundary circle) l := by
  rw [circle_boundary]; decide +kernel

/-- (C, AC) is a unit pair of the boundary, but after cancelling (A, AB) and then (B, BC) its
coefficient is 0, so it can no longer be cancelled. -/
theorem cyclic_pivot_destroyed :
    FiniteInput.boundary circle oC oAC = 1 ∧
      scheduleMatrix [(oA, oAB), (oB, oBC)] (FiniteInput.boundary circle) oC oAC = 0 := by
  rw [circle_boundary]; decide +kernel

end TDA.Persistence.Morse.IteratedCancellationExamples
