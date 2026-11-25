import TDA.Persistence.Morse.MorseDiagram
import TDA.Persistence.Morse.ReducerOrderExamples

/-!
# Fixtures for the reducer run on the Morse complex of a certified matching

Evaluations of `TDA.Persistence.Morse.MorseDiagram` over `ZMod 2`.

* Q1. The multi-grade square `square` with the certificate `sqCert`: four cancellations leave
  the critical positions A, AD, ACD in degrees and grades 0, 1, 2, with Morse differential
  `d ACD = AD`. The Morse run gives the occurrences `[⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩]`:
  the degree-1 diagram is `{(1, 2)}`, the degree-0 diagram `{(0, ⊤)}` and the degree-2 diagram
  is empty.
* Q2. The same occurrences and diagrams for the greedy certificate `genCert`, with critical
  positions D, AD, ACD.
* Q3. The ordinary run `FiniteInput.run square` on the boundary matrix of the square returns the
  same list, so it is `some sqCert.morseOccurrences` and `some genCert.morseOccurrences`; through
  `morseDiagram_eq_dgm`, Q1 gives the sublevel diagrams `dgm` of the square in degrees 1 and 0.
* Q4. The path of fixture R2 of `TDA.Persistence.Morse.ReducerOrderExamples`, all at grade 0,
  with the certificate `pathCert`: the pivot pair of the Morse run has equal grades and is
  dropped, and the run gives the single essential occurrence `⟨0, 0, .essential⟩`, as does
  `FiniteInput.run path`.
* Q5. The tie-order complex F4 of `TDA.Persistence.Morse.UnitCancellationExamples` and its
  cancellation of fixture R1: both runs give no occurrence. In reducer order a, r, s, b, F4 has
  the pivot pairs `(a, s)` and `(r, b)`, and its cancellation the pair `(r, s)`; all grades are
  0, so every pair is dropped and no index is essential.
* Q6. The path of Q4 in the reversed order of its critical positions, `dualOrder`: the reducer
  order becomes C, A, AB, and the essential generator is C instead of A, while the occurrence
  list is unchanged, which is consistent with `reducerOccurrences_perm_of_linearOrder` (a
  permutation).

* Q7. The complex `xD` on `Fin 4` with `d e = a` and `d f = b`, with `e`, `f` tied at grade 2 and
  degree 1: the natural order gives the occurrence list `[(0, 0, 2), (0, 1, 2)]` as (degree, birth,
  death) and the reversed order gives the same two occurrences in the other order, so the lists
  differ, they are permutations of each other, and the diagrams are equal in every degree.

Occurrence lists, diagram points, sorts and essential indices are evaluated by kernel `decide`,
after rewriting a Morse differential to its written-out form (`sqCert_morseDifferential`,
`genCert_morseDifferential`, `pathCert_morseDifferential`) or a boundary matrix with
`boundary_eq_coverIncidence`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.MorseDiagramExamples

open TDA.Persistence.Reduction TDA.Persistence.Reduction.FiniteInput
open TDA.Persistence.Morse.Cancellation TDA.Persistence.Morse.MatchingInput
open TDA.Persistence.Morse.ReducerOrder TDA.Persistence.Morse.ReducerDiagram
open TDA.Persistence.Morse.FiniteInputMatchingExamples (square square_valid)
open TDA.Persistence.Morse.MatchingScheduleExamples (sqCert genCert
  sqCert_morseDifferential genCert_morseDifferential)
open TDA.Persistence.Morse.UnitCancellationExamples (wD wDegree wGrade)
open TDA.Persistence.Morse.ReducerOrderExamples (rDegree rGrade path path_valid pathCert
  pathCert_morseDifferential PC cA cC cAB pDegree pGrade)

/-! ## Q1. The square with `sqCert` -/

/-- The Morse run of `sqCert` gives the bar `(1, 2)` in degree 1 and the essential `(0, ⊤)` in
degree 0. -/
theorem sqCert_morseOccurrences :
    sqCert.morseOccurrences = [⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] := by
  rw [CertifiedMatching.morseOccurrences, sqCert_morseDifferential]; decide +kernel

/-- The diagrams of the Morse run of `sqCert` in degrees 1, 0 and 2. -/
theorem sqCert_morseDiagram :
    (sqCert.morseDiagram 1).points = {(1, 2)} ∧ (sqCert.morseDiagram 0).points = {(0, ⊤)} ∧
      (sqCert.morseDiagram 2).points = 0 := by
  rw [CertifiedMatching.morseDiagram, CertifiedMatching.morseDiagram,
    CertifiedMatching.morseDiagram, sqCert_morseDifferential]; decide +kernel

/-! ## Q2. The square with `genCert` -/

/-- The Morse run of the greedy certificate `genCert` gives the same occurrences. -/
theorem genCert_morseOccurrences :
    genCert.morseOccurrences = [⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] := by
  rw [CertifiedMatching.morseOccurrences, genCert_morseDifferential]; decide +kernel

/-- The diagrams of the Morse run of `genCert` in degrees 1, 0 and 2. -/
theorem genCert_morseDiagram :
    (genCert.morseDiagram 1).points = {(1, 2)} ∧ (genCert.morseDiagram 0).points = {(0, ⊤)} ∧
      (genCert.morseDiagram 2).points = 0 := by
  rw [CertifiedMatching.morseDiagram, CertifiedMatching.morseDiagram,
    CertifiedMatching.morseDiagram, genCert_morseDifferential]; decide +kernel

/-! ## Q3. The ordinary run on the square -/

/-- The ordinary reducer run on the boundary matrix of the square. -/
theorem square_occurrences :
    FiniteInput.occurrences square = [⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] := by
  rw [← occurrences_boundary, boundary_eq_coverIncidence]; decide +kernel

/-- `FiniteInput.run square` returns the occurrences of `square_occurrences`. -/
theorem square_run : run square = some [⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩] :=
  (run_eq_some_iff _ _).mpr ⟨square_valid, square_occurrences.symm⟩

/-- The ordinary run on the square returns the Morse run of `sqCert`. -/
theorem square_run_eq_sqCert : run square = some sqCert.morseOccurrences := by
  rw [square_run, sqCert_morseOccurrences]

/-- The ordinary run on the square returns the Morse run of `genCert`. -/
theorem square_run_eq_genCert : run square = some genCert.morseOccurrences := by
  rw [square_run, genCert_morseOccurrences]

/-- The sublevel diagrams `dgm` of the square in degrees 1 and 0, read off the Morse run of
`sqCert` through `morseDiagram_eq_dgm`. -/
theorem square_dgm_of_morseDiagram :
    letI := faceFintype square square_valid
    (dgm (ZMod 2) (gradeFilter square square_valid) 1).points = {(1, 2)} ∧
      (dgm (ZMod 2) (gradeFilter square square_valid) 0).points = {(0, ⊤)} := by
  let := faceFintype square square_valid
  rw [← sqCert.morseDiagram_eq_dgm square_valid 1, ← sqCert.morseDiagram_eq_dgm square_valid 0]
  exact ⟨sqCert_morseDiagram.1, sqCert_morseDiagram.2.1⟩

/-! ## Q4. The path with `pathCert` -/

/-- The Morse run of `pathCert` drops its equal-grade pivot pair and keeps the essential
`(0, ⊤)`. -/
theorem pathCert_morseOccurrences : pathCert.morseOccurrences = [⟨0, 0, .essential⟩] := by
  rw [CertifiedMatching.morseOccurrences, pathCert_morseDifferential]; decide +kernel

/-- `FiniteInput.run path` returns the single essential occurrence. -/
theorem path_run : run path = some [⟨0, 0, .essential⟩] :=
  (run_eq_some_iff _ _).mpr ⟨path_valid, by
    rw [← occurrences_boundary, boundary_eq_coverIncidence]; decide +kernel⟩

/-- The ordinary run on the path returns the Morse run of `pathCert`. -/
theorem path_run_eq_pathCert : run path = some pathCert.morseOccurrences := by
  rw [path_run, pathCert_morseOccurrences]

/-! ## Q5. The tie-order complex F4 -/

/-- The reducer runs on the F4 complex and on its cancellation of `(a, b)` give no occurrence:
every generator lies in a pivot pair (`(a, s)` and `(r, b)` on F4, `(r, s)` after the
cancellation), so there is no essential index, and all generators have grade 0, so every pivot
pair is dropped. -/
theorem tie_reducerOccurrences :
    reducerOccurrences wDegree wGrade wD = [] ∧
      reducerOccurrences rDegree rGrade (reducedDifferential wD 0 3) = [] := by
  decide +kernel

/-! ## Q6. The reversed tie order on the path -/

/-- The reversed linear order of the critical positions of `pathCert`. -/
abbrev dualOrder : LinearOrder PC := inferInstanceAs (LinearOrder PCᵒᵈ)

/-- In the reversed order, the reducer order is C, A, AB. -/
theorem path_dual_sortedGenerators :
    @sortedGenerators PC dualOrder pDegree pGrade _ = [cC, cA, cAB] := by
  decide +kernel

/-- The essential generator is A in the inherited order and C in the reversed order. -/
theorem path_dual_essential :
    (essentialIndices (reducerMatrix pDegree pGrade pathCert.morseDifferential)).map
        (reducerEquiv pDegree pGrade) = [cA] ∧
      (essentialIndices (@reducerMatrix PC dualOrder _ _ pDegree pGrade
        pathCert.morseDifferential)).map (@reducerEquiv PC dualOrder pDegree pGrade _) =
        [cC] := by
  rw [pathCert_morseDifferential]; decide +kernel

/-- In the reversed order, the occurrence list is unchanged. -/
theorem path_dual_reducerOccurrences :
    @reducerOccurrences PC dualOrder _ _ _ _ pDegree pGrade pathCert.morseDifferential =
      [⟨0, 0, .essential⟩] := by
  rw [pathCert_morseDifferential]; decide +kernel

/-- The two occurrence lists are permutations of each other, by
`reducerOccurrences_perm_of_linearOrder`. -/
theorem path_dual_perm :
    (@reducerOccurrences PC dualOrder _ _ _ _ pDegree pGrade pathCert.morseDifferential).Perm
      pathCert.morseOccurrences :=
  reducerOccurrences_perm_of_linearOrder dualOrder inferInstance
    (pathCert.isFilteredDifferential_morseDifferential path_valid)

/-! ## Q7. Two tie orders with different occurrence lists and equal diagrams -/

/-- Generators `a, b, e, f = 0, 1, 2, 3` with `d e = a` and `d f = b`. -/
def xD : Matrix (Fin 4) (Fin 4) (ZMod 2) := fun r c =>
  if (r = 0 ∧ c = 2) ∨ (r = 1 ∧ c = 3) then 1 else 0

/-- `a`, `b` in degree 0 and `e`, `f` in degree 1. -/
def xDegree : Fin 4 → ℕ := fun i => i.val / 2

/-- `a` at grade 0, `b` at grade 1, and `e`, `f` at grade 2. -/
def xGrade : Fin 4 → ℤ := fun i => if i.val < 2 then (i.val : ℤ) else 2

/-- `xD` is a filtered differential for `xDegree` and `xGrade`. -/
theorem xD_isFilteredDifferential : IsFilteredDifferential xDegree xGrade xD :=
  ⟨⟨by decide +kernel, fun r c => by fin_cases r <;> fin_cases c <;> decide +kernel⟩,
    by decide +kernel⟩

/-- The reversed linear order of the four generators; `e` and `f` have equal grade and degree, so
their order is a tie, broken by the linear order. -/
abbrev xDual : LinearOrder (Fin 4) := inferInstanceAs (LinearOrder (Fin 4)ᵒᵈ)

/-- In the natural order the pivot pairs are `(a, e)` then `(b, f)`: the occurrence list is
`[(0, 0, 2), (0, 1, 2)]` as (degree, birth, death). -/
theorem tie_occurrences_natural :
    reducerOccurrences xDegree xGrade xD = [⟨0, 0, .finite 2⟩, ⟨0, 1, .finite 2⟩] := by
  decide +kernel

/-- In the reversed order the pivot pairs are `(b, f)` then `(a, e)`: the same two occurrences in
the other order. -/
theorem tie_occurrences_dual :
    @reducerOccurrences (Fin 4) xDual _ _ _ _ xDegree xGrade xD =
      [⟨0, 1, .finite 2⟩, ⟨0, 0, .finite 2⟩] := by
  decide +kernel

/-- The two occurrence lists differ as lists, though they are permutations of each other, and the
diagrams are equal in every degree. -/
theorem tie_occurrences_ne_diagram_eq :
    reducerOccurrences xDegree xGrade xD ≠
        @reducerOccurrences (Fin 4) xDual _ _ _ _ xDegree xGrade xD ∧
      (@reducerOccurrences (Fin 4) xDual _ _ _ _ xDegree xGrade xD).Perm
        (reducerOccurrences xDegree xGrade xD) ∧
      ∀ p, @reducerDiagram (Fin 4) xDual _ _ _ _ xDegree xGrade xD p =
        reducerDiagram xDegree xGrade xD p := by
  refine ⟨?_, ?_, fun p => reducerDiagram_eq_of_linearOrder xDual inferInstance
    xD_isFilteredDifferential p⟩
  · rw [tie_occurrences_natural, tie_occurrences_dual]; decide +kernel
  · exact reducerOccurrences_perm_of_linearOrder xDual inferInstance xD_isFilteredDifferential

end TDA.Persistence.Morse.MorseDiagramExamples
