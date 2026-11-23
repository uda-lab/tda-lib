import TDA.Persistence.Morse.ReducerOrder
import TDA.Persistence.Morse.UnitCancellationExamples
import TDA.Persistence.Morse.MatchingScheduleExamples

/-!
# Fixtures for the reducer order

Evaluations of `TDA.Persistence.Morse.ReducerOrder` over `ZMod 2`.

* R1. The tie-order complex F4 of `TDA.Persistence.Morse.UnitCancellationExamples`: at one
  grade, `a < s < r < b` with `d s = a` and `d b = a + r`. After cancelling `(a, b)` the reduced
  differential is `d' s = r`. In the inherited survivor order `s, r` it is not strictly upper
  triangular; the reducer order is `r, s`, in which it is.
* R2. The path A–B–C at grade 0, listed A, B, AB, C, BC, with the certified matching
  `(B, BC)`. The critical generators are A, AB, C and the Morse differential is
  `d AB = A + C`. In the inherited position order A, AB, C it is not strictly upper triangular;
  the reducer order is A, C, AB, in which it is. Sorting the enumeration AB, C, A gives the same
  order, an instance of `sortList_eq_of_perm`.
* R3. The multi-grade square with the certificates `sqCert` and `genCert` of
  `TDA.Persistence.Morse.MatchingScheduleExamples`. The reducer orders are A, AD, ACD and
  D, AD, ACD with grades 0, 1, 2, and the Morse differential in the reducer order has the single
  entry in row 1 and column 2.

The sorts, the critical positions and the matrices in the reducer order are evaluated by kernel
`decide`. A Morse differential is first rewritten to its written-out form
(`pathCert_morseDifferential`, which rewrites with `boundary_eq_coverIncidence`, or the S1 and
S2 theorems of `TDA.Persistence.Morse.MatchingScheduleExamples`). The two inherited orders fail
strict triangularity at an explicit entry, and the strict triangularity of the reducer orders is
derived from `strictBoundary_reducerMatrix`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.ReducerOrderExamples

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation
open TDA.Persistence.Morse.MatchingInput TDA.Persistence.Morse.ReducerOrder
open TDA.Persistence.Morse.UnitCancellationExamples (wD wDegree wGrade wS wR
  tie_isFilteredDifferential tie_isUnitPair)
open TDA.Persistence.Morse.FiniteInputMatchingExamples (square)
open TDA.Persistence.Morse.IteratedCancellationExamples (qA qD qAD qACD)
open TDA.Persistence.Morse.MatchingScheduleExamples (sqCert genCert
  sqCert_morseDifferential genCert_morseDifferential)

/-! ## R1. The tie order of F4 -/

/-- The survivors of the F4 cancellation of `(a, b) = (0, 3)`. -/
abbrev W := PairSurvivor (0 : Fin 4) 3

/-- The inherited degrees of the survivors. -/
def rDegree : W → ℕ := wDegree ∘ Subtype.val

/-- The inherited grades of the survivors. -/
def rGrade : W → ℤ := wGrade ∘ Subtype.val

/-- The reduced differential of the F4 cancellation is a filtered differential. -/
theorem tie_isFilteredDifferential_reduced :
    IsFilteredDifferential rDegree rGrade (reducedDifferential wD 0 3) :=
  isFilteredDifferential_reduced tie_isFilteredDifferential tie_isUnitPair rfl

/-- In the inherited survivor order `s, r`, the reduced differential is not strictly upper
triangular. -/
theorem tie_inherited_not_strictBoundary :
    ¬ StrictBoundary ((reducedDifferential wD 0 3).submatrix [wS, wR].get [wS, wR].get) :=
  fun h => absurd (h ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide +kernel)) (by decide)

/-- The reducer order of the survivors is `r, s`. -/
theorem tie_sortedGenerators : sortedGenerators rDegree rGrade = [wR, wS] := by
  decide +kernel

/-- In the reducer order, the reduced differential has the single entry `d' s = r` in row 0
and column 1. -/
theorem tie_reducerMatrix :
    reducerMatrix rDegree rGrade (reducedDifferential wD 0 3) =
      Matrix.of fun i j => if i.val = 0 ∧ j.val = 1 then 1 else 0 := by
  decide +kernel

/-- In the reducer order, the reduced differential is strictly upper triangular. -/
theorem tie_strictBoundary :
    StrictBoundary (reducerMatrix rDegree rGrade (reducedDifferential wD 0 3)) :=
  strictBoundary_reducerMatrix tie_isFilteredDifferential_reduced

/-! ## R2. A path with a certified matching -/

/-- The path A–B–C at grade 0, listed A, B, AB, C, BC. -/
def path : FiniteInput.Input := [({0}, 0), ({1}, 0), ({0, 1}, 0), ({2}, 0), ({1, 2}, 0)]

/-- `path` is a valid finite input. -/
theorem path_valid : FiniteInput.Valid path :=
  (FiniteInput.validBool_iff _).mp (by decide +kernel)

/-- The positions of `path`. -/
abbrev P := Fin path.length

/-- Position of A. -/
def pA : P := ⟨0, by decide⟩
/-- Position of B. -/
def pB : P := ⟨1, by decide⟩
/-- Position of AB. -/
def pAB : P := ⟨2, by decide⟩
/-- Position of C. -/
def pC : P := ⟨3, by decide⟩
/-- Position of BC. -/
def pBC : P := ⟨4, by decide⟩

/-- The matching `(B, BC)`, certified by the rank A 1, B 1, AB 0, C 3, BC 2. -/
def pathCert : CertifiedMatching path where
  pairs := [(pB, pBC)]
  rank := fun i => [1, 1, 0, 3, 2].getD i.val 0
  isMatching := by decide +kernel
  isTopologicalRank := by decide +kernel

/-- The critical positions of `pathCert` are A, AB and C. -/
theorem pathCert_critical : pathCert.critical = [pA, pAB, pC] := by decide +kernel

/-- The Morse carrier of `pathCert`. -/
abbrev PC := Critical pathCert.schedule

/-- The critical generator A. -/
def cA : PC := ⟨pA, by decide +kernel⟩
/-- The critical generator AB. -/
def cAB : PC := ⟨pAB, by decide +kernel⟩
/-- The critical generator C. -/
def cC : PC := ⟨pC, by decide +kernel⟩

/-- The inherited degrees of the critical generators. -/
def pDegree : PC → ℕ := FiniteInput.degree path ∘ Subtype.val

/-- The inherited grades of the critical generators. -/
def pGrade : PC → ℤ := (fun i => (path.get i).2) ∘ Subtype.val

/-- The Morse differential `d AB = A + C`, written out. -/
def pDiff : Matrix PC PC (ZMod 2) := fun r s =>
  if s.val = pAB ∧ (r.val = pA ∨ r.val = pC) then 1 else 0

/-- The Morse differential of `pathCert` is `pDiff`. -/
theorem pathCert_morseDifferential : pathCert.morseDifferential = pDiff := by
  rw [CertifiedMatching.morseDifferential, boundary_eq_coverIncidence]; decide +kernel

/-- In the inherited position order A, AB, C, the Morse differential is not strictly upper
triangular: `C` occurs in `d AB` but is listed after it. -/
theorem path_inherited_not_strictBoundary :
    ¬ StrictBoundary (pathCert.morseDifferential.submatrix [cA, cAB, cC].get
      [cA, cAB, cC].get) := by
  rw [pathCert_morseDifferential]
  exact fun h => absurd (h ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide +kernel)) (by decide)

/-- The reducer order of the critical generators is A, C, AB. -/
theorem path_sortedGenerators : sortedGenerators pDegree pGrade = [cA, cC, cAB] := by
  decide +kernel

/-- The sort does not depend on the enumeration: AB, C, A also sorts to A, C, AB. -/
theorem path_sortList : sortList pDegree pGrade [cAB, cC, cA] = [cA, cC, cAB] := by
  decide +kernel

/-- In the reducer order, the Morse differential has the entries in rows 0 and 1 of
column 2. -/
theorem path_reducerMatrix :
    reducerMatrix pDegree pGrade pathCert.morseDifferential =
      Matrix.of fun i j => if j.val = 2 ∧ i.val < 2 then 1 else 0 := by
  rw [pathCert_morseDifferential]; decide +kernel

/-- In the reducer order, the Morse differential of `pathCert` is strictly upper triangular. -/
theorem path_strictBoundary :
    StrictBoundary (reducerMatrix pDegree pGrade pathCert.morseDifferential) :=
  strictBoundary_reducerMatrix (pathCert.isFilteredDifferential_morseDifferential path_valid)

/-! ## R3. The square -/

/-- The inherited degrees of the critical generators of a certificate on the square. -/
def sDegree (c : CertifiedMatching square) : Critical c.schedule → ℕ :=
  FiniteInput.degree square ∘ Subtype.val

/-- The inherited grades of the critical generators of a certificate on the square. -/
def sGrade (c : CertifiedMatching square) : Critical c.schedule → ℤ :=
  (fun i => (square.get i).2) ∘ Subtype.val

/-- The reducer order of `sqCert` is A, AD, ACD, with grades 0, 1, 2. -/
theorem sqCert_sortedGenerators :
    (sortedGenerators (sDegree sqCert) (sGrade sqCert)).map Subtype.val = [qA, qAD, qACD] ∧
      (sortedGenerators (sDegree sqCert) (sGrade sqCert)).map (sGrade sqCert) = [0, 1, 2] := by
  decide +kernel

/-- The reducer order of `genCert` is D, AD, ACD, with grades 0, 1, 2. -/
theorem genCert_sortedGenerators :
    (sortedGenerators (sDegree genCert) (sGrade genCert)).map Subtype.val = [qD, qAD, qACD] ∧
      (sortedGenerators (sDegree genCert) (sGrade genCert)).map (sGrade genCert) = [0, 1, 2] := by
  decide +kernel

/-- In the reducer order, the Morse differential of `sqCert` has the single entry in row 1 and
column 2. -/
theorem sqCert_reducerMatrix :
    reducerMatrix (sDegree sqCert) (sGrade sqCert) sqCert.morseDifferential =
      Matrix.of fun i j => if i.val = 1 ∧ j.val = 2 then 1 else 0 := by
  rw [sqCert_morseDifferential]; decide +kernel

/-- In the reducer order, the Morse differential of `genCert` has the single entry in row 1 and
column 2. -/
theorem genCert_reducerMatrix :
    reducerMatrix (sDegree genCert) (sGrade genCert) genCert.morseDifferential =
      Matrix.of fun i j => if i.val = 1 ∧ j.val = 2 then 1 else 0 := by
  rw [genCert_morseDifferential]; decide +kernel

end TDA.Persistence.Morse.ReducerOrderExamples
