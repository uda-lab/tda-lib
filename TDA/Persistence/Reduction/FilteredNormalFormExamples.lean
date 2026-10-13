import TDA.Persistence.Reduction.FilteredNormalForm

/-! Small boundary matrices exercising the filtered normal-form contract. -/

namespace TDA.Persistence.Reduction

private def emptyBoundary : Matrix (Fin 0) (Fin 0) ℚ := 0

private theorem empty_square : emptyBoundary * emptyBoundary = 0 := by
  ext i
  exact Fin.elim0 i

private theorem empty_strict : StrictBoundary emptyBoundary := by
  intro i
  exact Fin.elim0 i

private theorem empty_degree (degree : Fin 0 → ℕ) :
    LowersDegree degree emptyBoundary := by
  intro i
  exact Fin.elim0 i

private example (degree : Fin 0 → ℕ) :
    let ops := matrixReductionTrace emptyBoundary
    let R := replay emptyBoundary ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = emptyBoundary * V ∧ TraceChangeCertificate degree V W ∧
      LowersDegree degree R ∧ StrictBoundary R ∧ DistinctPivots R ∧
      (∀ j i, columnPivot (R.col j) = some i → columnPivot (R.col i) = none) :=
  matrixReductionTrace_normalForm_input degree emptyBoundary empty_square
    empty_strict (empty_degree degree)

private theorem empty_homology_map_rank (degree : Fin 0 → ℕ) (p : ℕ) :
    let ops := matrixReductionTrace emptyBoundary
    let R := replay emptyBoundary ops
    let V := traceChange ops
    let W := traceChangeInv ops
    let h := matrixReductionTrace_normalForm_input degree emptyBoundary empty_square
      empty_strict (empty_degree degree)
    Module.finrank ℚ (LinearMap.range
      (originalHomologyMap degree emptyBoundary R V W empty_square h.1 h.2.1
        h.2.2.1 h.2.2.2.2.1 p 0 0)) = 0 := by
  dsimp only
  have h := matrixReductionTrace_normalForm_input degree emptyBoundary empty_square
    empty_strict (empty_degree degree)
  have hr := originalHomologyMap_rank_formula degree emptyBoundary _ _ _
    empty_square h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 p 0 0 (le_refl 0) (le_refl 0)
  simpa [deathSurvivorFinset, essentialSurvivorFinset] using hr

private def zeroMixed : Matrix (Fin 3) (Fin 3) ℚ := 0
private def mixedDegree : Fin 3 → ℕ := fun i => if i.val = 1 then 2 else 0

private theorem zeroMixed_square : zeroMixed * zeroMixed = 0 := by
  simp [zeroMixed]

private theorem zeroMixed_strict : StrictBoundary zeroMixed := by
  simp [StrictBoundary, zeroMixed]

private theorem zeroMixed_degree : LowersDegree mixedDegree zeroMixed := by
  simp [LowersDegree, zeroMixed]

private theorem zeroMixed_all_essential (i : Fin 3) : IsEssential zeroMixed i := by
  constructor
  · exact (columnPivot_none_iff _).2 (by intro r; simp [zeroMixed])
  · rintro ⟨j, hj⟩
    have hz := (columnPivot_none_iff (zeroMixed.col j)).2
      (by intro r; simp [zeroMixed])
    rw [hz] at hj
    cases hj

private theorem zeroMixed_mixed_essential_counts :
    (essentialSurvivorFinset mixedDegree zeroMixed 0 3).card = 2 ∧
      (essentialSurvivorFinset mixedDegree zeroMixed 2 3).card = 1 := by
  classical
  have h0 : essentialSurvivorFinset mixedDegree zeroMixed 0 3 =
      ({0, 2} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> simp [essentialSurvivorFinset, zeroMixed_all_essential, mixedDegree]
  have h2 : essentialSurvivorFinset mixedDegree zeroMixed 2 3 =
      ({1} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> simp [essentialSurvivorFinset, zeroMixed_all_essential, mixedDegree]
  simp [h0, h2]

private example :
    let ops := matrixReductionTrace zeroMixed
    let R := replay zeroMixed ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = zeroMixed * V ∧ TraceChangeCertificate mixedDegree V W ∧
      LowersDegree mixedDegree R ∧ StrictBoundary R ∧ DistinctPivots R ∧
      (∀ j i, columnPivot (R.col j) = some i → columnPivot (R.col i) = none) :=
  matrixReductionTrace_normalForm_input mixedDegree zeroMixed zeroMixed_square
    zeroMixed_strict zeroMixed_degree

/-- A nonunit coefficient and a repeated row force a genuine column change.
The row-zero generators have degree zero boundary. -/
private def repeatedRow : Matrix (Fin 3) (Fin 3) ℚ :=
  fun r c => if r.val = 0 then if c.val = 1 then 2 else if c.val = 2 then 3 else 0 else 0

private def repeatedDegree : Fin 3 → ℕ := fun i => if i.val = 0 then 0 else 1

private theorem repeated_square : repeatedRow * repeatedRow = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem repeated_strict : StrictBoundary repeatedRow := by
  intro r c h
  fin_cases r <;> fin_cases c <;> simp [repeatedRow] at h ⊢

private theorem repeated_degree : LowersDegree repeatedDegree repeatedRow := by
  intro r c h
  fin_cases r <;> fin_cases c <;> simp [repeatedRow, repeatedDegree] at h ⊢

private theorem repeated_pivot :
    columnPivot (repeatedRow.col (1 : Fin 3)) = some (0 : Fin 3) := by
  decide +kernel

private theorem repeated_zero_column : repeatedRow.col (0 : Fin 3) = 0 := by
  ext r
  fin_cases r <;> decide +kernel

private example :
    let ops := matrixReductionTrace repeatedRow
    let R := replay repeatedRow ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = repeatedRow * V ∧ TraceChangeCertificate repeatedDegree V W ∧
      LowersDegree repeatedDegree R ∧ StrictBoundary R ∧ DistinctPivots R ∧
      (∀ j i, columnPivot (R.col j) = some i → columnPivot (R.col i) = none) :=
  matrixReductionTrace_normalForm_input repeatedDegree repeatedRow repeated_square
    repeated_strict repeated_degree

private theorem repeated_change_nontrivial :
    traceChange (matrixReductionTrace repeatedRow) (1 : Fin 3) (2 : Fin 3) = -3 / 2 := by
  decide +kernel

/-- The two-generator calculation works for every field and every nonzero
coefficient, including coefficients other than one. -/
private def twoGenerator {F : Type*} [Field F] (c : F) :
    Matrix (Fin 2) (Fin 2) F :=
  fun r j => if r.val = 0 ∧ j.val = 1 then c else 0

private theorem twoGenerator_pivot {F : Type*} [Field F] [DecidableEq F]
    (c : F) (hc : c ≠ 0) :
    columnPivot ((twoGenerator c).col (1 : Fin 2)) = some (0 : Fin 2) := by
  apply (columnPivot_some_iff _ _).2
  constructor
  · simpa [twoGenerator] using hc
  · intro r hr
    fin_cases r <;> simp [twoGenerator] at hr ⊢

private theorem twoGenerator_pair_interval {F : Type*} [Field F] [DecidableEq F]
    (c : F) (hc : c ≠ 0) (t : Fin 3) :
    (pairedInterval (twoGenerator c) (by
      intro r j h
      fin_cases r <;> fin_cases j <;> simp [twoGenerator] at h ⊢)
      1 0 (twoGenerator_pivot c hc)).alive t ↔
      0 < t.val ∧ t.val ≤ 1 := by
  exact pairedInterval_alive_iff _ _ _ _ _ t

private theorem twoGenerator_normalized {F : Type*} [Field F] [DecidableEq F]
    (c : F) (hc : c ≠ 0) :
    normalColumn (twoGenerator c) (1 : Matrix (Fin 2) (Fin 2) F) 0 =
      Pi.single (0 : Fin 2) 1 := by
  have hp : IsPivot (twoGenerator c) 0 := ⟨1, twoGenerator_pivot c hc⟩
  rw [normalColumn_pivot _ _ 0 hp]
  have hcol0 : columnPivot ((twoGenerator c).col (0 : Fin 2)) = none :=
    (columnPivot_none_iff _).2 (by intro r; simp [twoGenerator])
  have hj := deathOfPivot_unique (twoGenerator c) (by
    intro i j p hi hj
    fin_cases i <;> fin_cases j <;> simp_all [hcol0])
    0 1 hp (twoGenerator_pivot c hc)
  rw [hj]
  ext r
  fin_cases r <;> simp [twoGenerator, Pi.single_apply, hc]

private def interleaved : Matrix (Fin 4) (Fin 4) ℚ :=
  fun r c => if r.val = 0 ∧ c.val = 2 then 2 else
    if r.val = 1 ∧ c.val = 3 then 3 else 0

private def interleavedDegree : Fin 4 → ℕ :=
  fun i => if i.val < 2 then 0 else 1

private theorem interleaved_square : interleaved * interleaved = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem interleaved_strict : StrictBoundary interleaved := by
  intro r c h
  fin_cases r <;> fin_cases c <;> simp [interleaved] at h ⊢

private theorem interleaved_degree : LowersDegree interleavedDegree interleaved := by
  intro r c h
  fin_cases r <;> fin_cases c <;> simp [interleaved, interleavedDegree] at h ⊢

private theorem interleaved_distinct : DistinctPivots interleaved := by
  have h0 : columnPivot (interleaved.col (0 : Fin 4)) = none := by decide +kernel
  have h1 : columnPivot (interleaved.col (1 : Fin 4)) = none := by decide +kernel
  have h2 : columnPivot (interleaved.col (2 : Fin 4)) = some (0 : Fin 4) := by
    decide +kernel
  have h3 : columnPivot (interleaved.col (3 : Fin 4)) = some (1 : Fin 4) := by
    decide +kernel
  intro i j p hi hj
  fin_cases i <;> fin_cases j <;> simp_all [h0, h1, h2, h3] <;> omega

private theorem interleaved_pivot_zero : IsPivot interleaved (0 : Fin 4) := by
  exact ⟨2, by decide +kernel⟩

private theorem interleaved_death_zero :
    deathOfPivot interleaved 0 interleaved_pivot_zero = (2 : Fin 4) :=
  deathOfPivot_unique interleaved interleaved_distinct 0 2 interleaved_pivot_zero
    (by decide +kernel)

private theorem interleaved_survives_before_death :
    aliveRepresentative interleavedDegree interleaved 0 2
      (Pi.single (0 : Fin 4) (1 : ℚ)) = Pi.single 0 1 := by
  apply aliveRepresentative_single_survives
  refine ⟨by simp [interleavedDegree], Or.inl ?_⟩
  exact (pivotAlive_iff interleaved 2 0 interleaved_pivot_zero).2
    (by simp [interleaved_death_zero])

private theorem interleaved_dies_at_death :
    aliveRepresentative interleavedDegree interleaved 0 3
      (Pi.single (0 : Fin 4) (1 : ℚ)) = 0 := by
  apply aliveRepresentative_single_dies
  intro h
  rcases h.2 with hp | he
  · obtain ⟨hi, _, hd⟩ := hp
    have hj := deathOfPivot_unique interleaved interleaved_distinct 0 2 hi
      (by decide +kernel)
    rw [hj] at hd
    omega
  · exact he.1.2 interleaved_pivot_zero

private theorem interleaved_trace_nil : matrixReductionTrace interleaved = [] := by
  decide +kernel

/-- The actual original-boundary homology map kills this pair at stage three.
The class is specified through the proved simultaneous coordinate equivalence. -/
private theorem interleaved_original_map_kills_pair :
    let ops := matrixReductionTrace interleaved
    let R := replay interleaved ops
    let V := traceChange ops
    let W := traceChangeInv ops
    let h := matrixReductionTrace_normalForm_input interleavedDegree interleaved
      interleaved_square interleaved_strict interleaved_degree
    let E₂ := originalHomologyEquivAlive interleavedDegree interleaved R V W
      interleaved_square h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 0 2
    let E₃ := originalHomologyEquivAlive interleavedDegree interleaved R V W
      interleaved_square h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 0 3
    ∀ x : originalHomology interleavedDegree interleaved R V W interleaved_square
      h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 0 2,
      (E₂ x).1 = Pi.single (0 : Fin 4) (1 : ℚ) →
      originalHomologyMap interleavedDegree interleaved R V W interleaved_square
        h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 0 2 3 x = 0 := by
  dsimp only
  intro x hx
  have hR : replay interleaved (matrixReductionTrace interleaved) = interleaved := by
    simp [interleaved_trace_nil, replay]
  let R := replay interleaved (matrixReductionTrace interleaved)
  let V := traceChange (matrixReductionTrace interleaved)
  let W := traceChangeInv (matrixReductionTrace interleaved)
  let h := matrixReductionTrace_normalForm_input interleavedDegree interleaved
    interleaved_square interleaved_strict interleaved_degree
  let E₂ := originalHomologyEquivAlive interleavedDegree interleaved R V W
    interleaved_square h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 0 2
  let E₃ := originalHomologyEquivAlive interleavedDegree interleaved R V W
    interleaved_square h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 0 3
  apply E₃.injective
  rw [originalHomologyMap_transport]
  rw [map_zero]
  apply Subtype.ext
  change aliveRepresentative interleavedDegree R 0 3
    ((originalHomologyEquivAlive interleavedDegree interleaved R V W
      interleaved_square h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 0 2) x).1 = 0
  rw [hx]
  dsimp only [R]
  rw [hR]
  exact interleaved_dies_at_death

private example :
    let ops := matrixReductionTrace interleaved
    let R := replay interleaved ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = interleaved * V ∧ TraceChangeCertificate interleavedDegree V W ∧
      LowersDegree interleavedDegree R ∧ StrictBoundary R ∧ DistinctPivots R ∧
      (∀ j i, columnPivot (R.col j) = some i → columnPivot (R.col i) = none) :=
  matrixReductionTrace_normalForm_input interleavedDegree interleaved interleaved_square
    interleaved_strict interleaved_degree

/-- Two disjoint pairs with an essential cycle strictly between their births.
Indices 0/3 and 2/4 pair; index 1 survives. -/
private def interleavedEssential : Matrix (Fin 5) (Fin 5) ℚ :=
  fun r c => if r.val = 0 ∧ c.val = 3 then 2 else
    if r.val = 2 ∧ c.val = 4 then 3 else 0

private def interleavedEssentialDegree : Fin 5 → ℕ :=
  fun i => if i.val < 3 then 0 else 1

private theorem interleavedEssential_square :
    interleavedEssential * interleavedEssential = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem interleavedEssential_strict : StrictBoundary interleavedEssential := by
  intro r c h
  fin_cases r <;> fin_cases c <;> simp [interleavedEssential] at h ⊢

private theorem interleavedEssential_degree :
    LowersDegree interleavedEssentialDegree interleavedEssential := by
  intro r c h
  fin_cases r <;> fin_cases c <;>
    simp [interleavedEssential, interleavedEssentialDegree] at h ⊢

private theorem interleavedEssential_pairs :
    columnPivot (interleavedEssential.col (3 : Fin 5)) = some (0 : Fin 5) ∧
    columnPivot (interleavedEssential.col (4 : Fin 5)) = some (2 : Fin 5) := by
  decide +kernel

private theorem interleavedEssential_unpaired :
    IsEssential interleavedEssential (1 : Fin 5) := by
  constructor
  · exact (columnPivot_none_iff _).2 (by intro r; simp [interleavedEssential])
  · rintro ⟨j, hj⟩
    have hn : ∀ q : Fin 5,
        columnPivot (interleavedEssential.col q) ≠ some (1 : Fin 5) := by
      intro q
      fin_cases q <;> decide +kernel
    exact hn j hj

private theorem interleavedEssential_cycle_survives :
    aliveRepresentative interleavedEssentialDegree interleavedEssential 0 5
      (Pi.single (1 : Fin 5) (1 : ℚ)) = Pi.single 1 1 := by
  apply aliveRepresentative_single_survives
  refine ⟨by simp [interleavedEssentialDegree], Or.inr ?_⟩
  exact ⟨interleavedEssential_unpaired, by decide⟩

/-- This square-zero input reduces to an `R` whose square is nonzero. The
normal-form theorem continues to use the original differential. -/
private def squareNonzeroAfterReduction : Matrix (Fin 4) (Fin 4) ℚ :=
  fun r c =>
    if c.val = 1 ∨ c.val = 2 then (if r.val = 0 then 1 else 0)
    else if c.val = 3 then (if r.val = 2 then 1 else if r.val = 1 then -1 else 0)
    else 0

private def squareNonzeroDegree : Fin 4 → ℕ :=
  fun i => if i.val = 0 then 0 else if i.val = 3 then 2 else 1

private theorem squareNonzero_input_square :
    squareNonzeroAfterReduction * squareNonzeroAfterReduction = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem squareNonzero_input_strict :
    StrictBoundary squareNonzeroAfterReduction := by
  intro r c h
  fin_cases r <;> fin_cases c <;> simp [squareNonzeroAfterReduction] at h ⊢

private theorem squareNonzero_input_degree :
    LowersDegree squareNonzeroDegree squareNonzeroAfterReduction := by
  intro r c h
  fin_cases r <;> fin_cases c <;>
    simp [squareNonzeroAfterReduction, squareNonzeroDegree] at h ⊢

private theorem squareNonzero_reduced_square :
    let R := replay squareNonzeroAfterReduction
      (matrixReductionTrace squareNonzeroAfterReduction)
    (R * R) (0 : Fin 4) (3 : Fin 4) = -1 := by
  decide +kernel

private theorem squareNonzero_paired_cycle_nonstandard :
    let R := replay squareNonzeroAfterReduction
      (matrixReductionTrace squareNonzeroAfterReduction)
    let V := traceChange (matrixReductionTrace squareNonzeroAfterReduction)
    (normalColumn R V (2 : Fin 4)) (1 : Fin 4) = -1 := by
  let R := replay squareNonzeroAfterReduction
    (matrixReductionTrace squareNonzeroAfterReduction)
  let V := traceChange (matrixReductionTrace squareNonzeroAfterReduction)
  have hji : columnPivot (R.col (3 : Fin 4)) = some (2 : Fin 4) := by
    decide +kernel
  have hp : IsPivot R (2 : Fin 4) := ⟨3, hji⟩
  have hpiv : DistinctPivots R := by
    intro i j p hi hj
    exact matrixReductionTrace_pivots_distinct squareNonzeroAfterReduction i j p hi hj
  have hdeath := deathOfPivot_unique R hpiv 2 3 hp hji
  dsimp only
  rw [normalColumn_pivot R V 2 hp, hdeath]
  change (R 2 3)⁻¹ * R 1 3 = -1
  decide +kernel

private example :
    let ops := matrixReductionTrace squareNonzeroAfterReduction
    let R := replay squareNonzeroAfterReduction ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = squareNonzeroAfterReduction * V ∧
      TraceChangeCertificate squareNonzeroDegree V W ∧
      LowersDegree squareNonzeroDegree R ∧ StrictBoundary R ∧ DistinctPivots R ∧
      (∀ j i, columnPivot (R.col j) = some i → columnPivot (R.col i) = none) :=
  matrixReductionTrace_normalForm_input squareNonzeroDegree
    squareNonzeroAfterReduction squareNonzero_input_square
    squareNonzero_input_strict squareNonzero_input_degree

end TDA.Persistence.Reduction
