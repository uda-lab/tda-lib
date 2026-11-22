import TDA.Persistence.Morse.MatchingSchedule
import TDA.Persistence.Morse.IteratedCancellationExamples
import TDA.Persistence.Morse.FiniteInputMatchingGeneration

/-!
# Fixtures for the pivot schedule of a certified matching

Evaluations of `TDA.Persistence.Morse.MatchingInput.CertifiedMatching.schedule` and
`CertifiedMatching.morseDifferential` on the multi-grade square `square` of
`TDA.Persistence.Morse.FiniteInputMatchingExamples` (positions 0–10 for A, B, C, D, AB, BC, CD,
AD, AC, ABC, ACD), over `ZMod 2`.

* S1. The certificate of `square_check`: the pairs of `squarePairs` with the rank
  10, 8, 6, 4, 9, 7, 5, 1, 2, 3, 0. Its schedule is `sqSchedule` of
  `TDA.Persistence.Morse.IteratedCancellationExamples`, while `squarePairs` in its own order is
  not a pivot schedule. The critical positions are A, AD, ACD, and the Morse differential has
  the single entry `d ACD = AD`.
* S2. The greedy certificate `generate square`. Its schedule is (AC, ABC), (A, AB), (B, BC),
  (C, CD); the critical positions are D, AD, ACD, and the Morse differential again has the
  single entry `d ACD = AD`.
* S3. A tie: the pairs of `squarePairs` with a rank that gives D and AC the same value 2. The
  stable sort keeps D before AC, so the schedule is (D, CD), (AC, ABC), (C, BC), (B, AB); it is a
  pivot schedule, as is `sqSchedule`, which has the tied pairs in the other order. The critical
  positions and the Morse differential are those of S1.

Every closed computation is a kernel `decide`; `sqMorseD_sqSchedule` is `rfl`, and the first
conjunct of `tieCert_isPivotSchedule` is `isPivotSchedule_schedule`. Each kernel `decide` on a
goal that mentions `FiniteInput.boundary square` runs after rewriting with
`boundary_eq_coverIncidence`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.MatchingScheduleExamples

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation
open TDA.Persistence.Morse.MatchingInput
open TDA.Persistence.Morse.FiniteInputMatchingExamples (square square_valid squarePairs)
open TDA.Persistence.Morse.IteratedCancellationExamples

/-- The Morse differential of the square fixtures on the critical generators of a schedule
`l`: the single entry `d ACD = AD`. For `sqSchedule` it is `sqCritD`. -/
def sqMorseD (l : List (Sq × Sq)) : Matrix (Critical l) (Critical l) (ZMod 2) := fun r s =>
  if r.val = qAD ∧ s.val = qACD then 1 else 0

/-- On `sqSchedule`, `sqMorseD` is `sqCritD`. -/
theorem sqMorseD_sqSchedule : sqMorseD sqSchedule = sqCritD := rfl

/-! ## S1. The certificate of `square_check` -/

/-- The rank of `square_check`: A 10, B 8, C 6, D 4, AB 9, BC 7, CD 5, AD 1, AC 2, ABC 3,
ACD 0. -/
def sqRank : Sq → ℕ := fun i => [10, 8, 6, 4, 9, 7, 5, 1, 2, 3, 0].getD i.val 0

/-- The pairs of `squarePairs`, certified by `sqRank`. -/
def sqCert : CertifiedMatching square where
  pairs := squarePairs
  rank := sqRank
  isMatching := by decide +kernel
  isTopologicalRank := by decide +kernel

/-- The lower faces AC, D, C, B of the pairs have ranks 2, 4, 6, 8. -/
theorem sqCert_lowerRanks :
    sqCert.rank qAC = 2 ∧ sqCert.rank qD = 4 ∧ sqCert.rank qC = 6 ∧ sqCert.rank qB = 8 := by
  decide +kernel

/-- The schedule of the certificate is `sqSchedule`: (AC, ABC), (D, CD), (C, BC), (B, AB). -/
theorem sqCert_schedule : sqCert.schedule = sqSchedule := by decide +kernel

/-- The certified pairs in their own order are not a pivot schedule. -/
theorem sqCert_pairs_not_isPivotSchedule :
    ¬ IsPivotSchedule sqGrade (FiniteInput.boundary square) sqCert.pairs := by
  rw [boundary_eq_coverIncidence]; decide +kernel

/-- The critical positions of the certificate are A, AD and ACD. -/
theorem sqCert_critical : sqCert.critical = [qA, qAD, qACD] := by decide +kernel

/-- The critical generators of the schedule are A, AD and ACD. -/
theorem sqCert_criticalSet : criticalSet sqCert.schedule = {qA, qAD, qACD} := by
  decide +kernel

/-- The Morse differential of the certificate: only `d ACD = AD`. -/
theorem sqCert_morseDifferential : sqCert.morseDifferential = sqMorseD sqCert.schedule := by
  rw [CertifiedMatching.morseDifferential, boundary_eq_coverIncidence]; decide +kernel

/-! ## S2. The greedy certificate -/

/-- The greedy certificate of the square. -/
def genCert : CertifiedMatching square := generate square

/-- The schedule of the greedy certificate: (AC, ABC), (A, AB), (B, BC), (C, CD), in
increasing rank 1, 2, 4, 6 of the lower face. -/
theorem genCert_schedule :
    genCert.schedule = [(qAC, qABC), (qA, qAB), (qB, qBC), (qC, qCD)] := by
  decide +kernel

/-- The critical positions of the greedy certificate are D, AD and ACD. -/
theorem genCert_critical : genCert.critical = [qD, qAD, qACD] := by decide +kernel

/-- The critical generators of the greedy schedule are D, AD and ACD. -/
theorem genCert_criticalSet : criticalSet genCert.schedule = {qD, qAD, qACD} := by
  decide +kernel

/-- The Morse differential of the greedy certificate: only `d ACD = AD`. -/
theorem genCert_morseDifferential :
    genCert.morseDifferential = sqMorseD genCert.schedule := by
  rw [CertifiedMatching.morseDifferential, boundary_eq_coverIncidence]; decide +kernel

/-! ## S3. A tie in the rank -/

/-- A rank of `squarePairs` with a tie between the lower faces D and AC: A 8, B 6, C 4, D 2,
AB 7, BC 5, CD 3, AD 1, AC 2, ABC 3, ACD 0. -/
def tieRank : Sq → ℕ := fun i => [8, 6, 4, 2, 7, 5, 3, 1, 2, 3, 0].getD i.val 0

/-- The pairs of `squarePairs`, certified by `tieRank`. -/
def tieCert : CertifiedMatching square where
  pairs := squarePairs
  rank := tieRank
  isMatching := by decide +kernel
  isTopologicalRank := by decide +kernel

/-- The lower faces D and AC have the same rank. -/
theorem tieCert_rank_eq : tieCert.rank qD = tieCert.rank qAC := by decide +kernel

/-- The stable sort keeps D before AC: (D, CD), (AC, ABC), (C, BC), (B, AB). -/
theorem tieCert_schedule :
    tieCert.schedule = [(qD, qCD), (qAC, qABC), (qC, qBC), (qB, qAB)] := by
  decide +kernel

/-- The tie schedule is a pivot schedule, by the general theorem and by direct evaluation. -/
theorem tieCert_isPivotSchedule :
    IsPivotSchedule sqGrade (FiniteInput.boundary square) tieCert.schedule ∧
      IsPivotSchedule sqGrade (FiniteInput.boundary square)
        [(qD, qCD), (qAC, qABC), (qC, qBC), (qB, qAB)] := by
  refine ⟨tieCert.isPivotSchedule_schedule square_valid, ?_⟩
  rw [boundary_eq_coverIncidence]; decide +kernel

/-- The critical positions of the tie certificate are A, AD and ACD. -/
theorem tieCert_critical : tieCert.critical = [qA, qAD, qACD] := by decide +kernel

/-- The Morse differential of the tie certificate: only `d ACD = AD`. -/
theorem tieCert_morseDifferential :
    tieCert.morseDifferential = sqMorseD tieCert.schedule := by
  rw [CertifiedMatching.morseDifferential, boundary_eq_coverIncidence]; decide +kernel

end TDA.Persistence.Morse.MatchingScheduleExamples
