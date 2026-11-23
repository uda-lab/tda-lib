import TDA.Persistence.Morse.ReducerOrder
import TDA.Persistence.DiagramRankUniqueness
import TDA.Persistence.Reduction.FiniteInput
import TDA.Persistence.FiniteRankProjectiveResolution

/-!
# The graded reducer output and its rank semantics

For a square matrix `D` over `Fin m`, `reduced D` is the reduced matrix
`replay D (matrixReductionTrace D)` of the column reducer of `TDA.Persistence.Reduction`. Over
`degree : Fin m → ℕ` and `grade : Fin m → ℤ`, `pivotPairs D` and `essentialIndices D` list its
pivot pairs `(i, j)` and its essential indices, `occurrences degree grade D` records them as
`FiniteInput.Occurrence`s at their grades, dropping the pairs with `grade i = grade j`, and
`diagram degree grade D p : Diagram ℤ` collects the points of degree `p`. These are computable,
and on the boundary matrix of a finite input `occurrences` and `diagram` are
`FiniteInput.occurrences` and `FiniteInput.outputDiagram` by definition (`occurrences_boundary`,
`diagram_boundary`).

Assume `D * D = 0`, `StrictBoundary D`, `LowersDegree degree D` and `Monotone grade`. The
indices of grade at most `a` are the first `stage grade a` indices, so the grade sublevel cycles
and boundaries are the reducer's prefix cycles and boundaries, and `prefixHomologyEquiv`
identifies sublevel homology with the reducer's `originalHomology`, naturally
(`originalHomology_kernel_eq_boundaries`, `originalHomologyMap_mk`). With the rank formula
`matrixReductionTrace_originalHomologyMap_rank_formula` and `countP_diagram`, the rank of the
structure map `a ≤ b` of `sublevelHomologyPModule degree grade D p` is the number of points
`(b', d)` of `diagram degree grade D p` with `b' ≤ a` and `b < d` (`rankOfStructureMap_eq_countP`).
Equal-grade pairs count for no `a ≤ b`. The diagram is positive, so by
`Diagram.eq_of_sliceCounts_eq` it is the only positive diagram with these slice counts
(`eq_diagram_of_rankCounts`).

For a filtered differential on a finite linearly ordered carrier over a field,
`reducerOccurrences` and `reducerDiagram` are the output on `reducerMatrix` of
`TDA.Persistence.Morse.ReducerOrder`; through `reducerHomologyIso` the same statements hold for
the ranks of the original complex (`rankOfStructureMap_eq_countP_reducerDiagram`,
`eq_reducerDiagram_of_rankCounts`).

This is a library derivation. The module runs no reducer on the Morse complex of a certified
matching and compares no diagram with `dgm`.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.ReducerDiagram

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation
open TDA.Persistence.Morse.ReducerOrder
open TDA.Persistence.Reduction.FiniteInput (Occurrence Death)

section Output

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

/-- The reduced matrix of the chronological reducer. -/
def reduced (D : Matrix (Fin m) (Fin m) k) : Matrix (Fin m) (Fin m) k :=
  replay D (matrixReductionTrace D)

/-- The pivot pairs `(i, j)` of the reduced matrix: one per nonzero reduced column `j`, with
pivot row `i`. -/
def pivotPairs (D : Matrix (Fin m) (Fin m) k) : List (Fin m × Fin m) :=
  (List.finRange m).filterMap fun j =>
    (columnPivot ((reduced D).col j)).map fun i => (i, j)

/-- The essential indices: zero reduced columns that are no pivot row. -/
def essentialIndices (D : Matrix (Fin m) (Fin m) k) : List (Fin m) :=
  (List.finRange m).filter fun i =>
    (columnPivot ((reduced D).col i)).isNone && !(pivotPairs D).any (fun q => q.1 == i)

/-- `(i, j)` is a pivot pair exactly when the reduced column `j` has pivot row `i`. -/
theorem mem_pivotPairs (D : Matrix (Fin m) (Fin m) k) (i j : Fin m) :
    (i, j) ∈ pivotPairs D ↔ columnPivot ((reduced D).col j) = some i := by
  unfold pivotPairs
  simp only [List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j', hj'⟩
    cases h : columnPivot ((reduced D).col j') with
    | none => simp [h] at hj'
    | some p =>
        simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj'
        obtain ⟨rfl, rfl⟩ := hj'
        exact h
  · intro h
    exact ⟨j, by simp [h]⟩

/-- The essential indices are the `IsEssential` indices of the reduced matrix. -/
theorem mem_essentialIndices (D : Matrix (Fin m) (Fin m) k) (i : Fin m) :
    i ∈ essentialIndices D ↔ IsEssential (reduced D) i := by
  simp only [essentialIndices, List.mem_filter, List.mem_finRange, true_and, IsEssential,
    IsPivot, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.any_eq_false, beq_iff_eq, Prod.forall]
  refine and_congr_right fun _ => ⟨fun h ⟨j, hj⟩ => h i j ((mem_pivotPairs D i j).mpr hj) rfl,
    fun h r j hq hr => h ⟨j, hr ▸ (mem_pivotPairs D r j).mp hq⟩⟩

/-- `StrictBoundary` is decidable, entry by entry. -/
instance decidableStrictBoundary (D : Matrix (Fin m) (Fin m) k) :
    Decidable (StrictBoundary D) :=
  @Fintype.decidableForallFintype _ _
    (fun _ => @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) _) _

/-- `LowersDegree` is decidable, entry by entry. -/
instance decidableLowersDegree (degree : Fin m → ℕ) (D : Matrix (Fin m) (Fin m) k) :
    Decidable (LowersDegree degree D) :=
  @Fintype.decidableForallFintype _ _
    (fun _ => @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) _) _

variable (degree : Fin m → ℕ) (grade : Fin m → ℤ)

/-- The occurrence of a pivot pair: none for an equal-grade pair. -/
def pairOccurrence (q : Fin m × Fin m) : Option Occurrence :=
  if grade q.1 = grade q.2 then none else
    some ⟨degree q.1, grade q.1, .finite (grade q.2)⟩

/-- The occurrences of the reducer output: pivot pairs at their grades, equal-grade pairs
dropped, and essential indices with essential death. -/
def occurrences (D : Matrix (Fin m) (Fin m) k) : List Occurrence :=
  (pivotPairs D).filterMap (pairOccurrence degree grade) ++
    (essentialIndices D).map fun i => ⟨degree i, grade i, .essential⟩

/-- The degree-`p` diagram of the reducer output over the grades. -/
def diagram (D : Matrix (Fin m) (Fin m) k) (p : ℕ) : Diagram ℤ where
  points := (((occurrences degree grade D).filter (fun o => o.degree = p) : List Occurrence) :
    Multiset Occurrence).map Occurrence.point
  offDiagonal := by
    intro q hq
    obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.mp hq
    have hmem : o ∈ occurrences degree grade D :=
      (List.mem_filter.mp (Multiset.mem_coe.mp ho)).1
    rcases List.mem_append.mp hmem with hf | he
    · obtain ⟨q, _, hq⟩ := List.mem_filterMap.mp hf
      unfold pairOccurrence at hq
      split_ifs at hq with hne
      cases hq
      simpa [Occurrence.point] using hne
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      simp [Occurrence.point]

/-- On the boundary matrix of a finite input, `occurrences` is `FiniteInput.occurrences`. -/
theorem occurrences_boundary (xs : FiniteInput.Input) :
    occurrences (FiniteInput.degree xs) (fun i => (xs.get i).2) (FiniteInput.boundary xs) =
      FiniteInput.occurrences xs :=
  rfl

/-- On the boundary matrix of a finite input, `diagram` is `FiniteInput.outputDiagram`. -/
theorem diagram_boundary (xs : FiniteInput.Input) (p : ℕ) :
    diagram (FiniteInput.degree xs) (fun i => (xs.get i).2) (FiniteInput.boundary xs) p =
      FiniteInput.outputDiagram xs p :=
  rfl

/-- The number of indices of grade at most `a`. -/
def stage (a : ℤ) : ℕ :=
  (Finset.univ.filter fun i => grade i ≤ a).card

variable {grade} in
/-- For monotone grades, the indices of grade at most `a` are those before `stage grade a`. -/
theorem grade_le_iff_lt_stage (hgrade : Monotone grade) (a : ℤ) (i : Fin m) :
    grade i ≤ a ↔ i.val < stage grade a := by
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter fun j => grade j ≤ a := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hgrade (Finset.mem_Iic.mp hj)).trans hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    exact this
  · intro hi
    by_contra hn
    have hsub : (Finset.univ.filter fun j => grade j ≤ a) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine Finset.mem_Iio.mpr (lt_of_not_ge fun hij => hn ?_)
      exact (hgrade hij).trans hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    exact absurd hi (not_lt.mpr this)

/-- `stage grade a` is at most the number of indices. -/
theorem stage_le (a : ℤ) : stage grade a ≤ m :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)

/-- `stage grade` is monotone. -/
theorem stage_mono {a b : ℤ} (hab : a ≤ b) : stage grade a ≤ stage grade b :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans hab

omit [DecidableEq k] in
private theorem countP_finRange (f : Fin m → Bool) :
    (List.finRange m).countP f = (Finset.univ.filter fun j => f j = true).card := by
  rw [Finset.card_def, Finset.filter_val, Fin.univ_def, ← Multiset.countP_eq_card_filter]
  simp

variable {grade} in
/-- **Slice counts as reducer counts.** For monotone grades and `a ≤ b`, the slice count of
`diagram` is the number of degree-`p` deaths of the prefix `stage grade a` that survive to
`stage grade b`, plus its degree-`p` essential births: the count of the reducer's rank formula
`matrixReductionTrace_originalHomologyMap_rank_formula`. -/
theorem countP_diagram (hgrade : Monotone grade) (D : Matrix (Fin m) (Fin m) k) (p : ℕ)
    {a b : ℤ} (hab : a ≤ b) :
    (diagram degree grade D p).points.countP (fun q => q.1 ≤ a ∧ (b : WithTop ℤ) < q.2) =
      (deathSurvivorFinset degree (reduced D) p (stage grade a) (stage grade b)).card +
        (essentialSurvivorFinset degree (reduced D) p (stage grade a)).card := by
  classical
  have hlt : ∀ c i, grade i ≤ c ↔ i.val < stage grade c := grade_le_iff_lt_stage hgrade
  have hge : ∀ c (j : Fin m), c < grade j ↔ stage grade c ≤ j.val := fun c j => by
    rw [← not_le, hlt c j, not_lt]
  have hess := mem_essentialIndices D
  simp only [diagram, Multiset.map_coe, Multiset.coe_countP, List.countP_map, occurrences,
    List.filter_append, List.countP_append, List.countP_filterMap, List.countP_filter]
  unfold pivotPairs
  rw [List.countP_filterMap, countP_finRange]
  unfold essentialIndices at hess ⊢
  rw [List.countP_filter, countP_finRange]
  unfold deathSurvivorFinset essentialSurvivorFinset
  congr 1 <;> congr 1 <;> ext j <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · rcases h : columnPivot ((reduced D).col j) with _ | i
    · simp
    · by_cases hg : grade i = grade j
      · simp only [Option.map_some, Option.getD_some, pairOccurrence, hg, ite_true,
          Option.map_none, Option.getD_none, Bool.false_eq_true, false_iff, not_exists, not_and,
          Option.some.injEq]
        rintro _ rfl _ hi hj
        rw [← hlt, hg] at hi
        rw [← hge] at hj
        exact absurd (hi.trans hab) (not_le.mpr hj)
      · simp only [Option.map_some, Option.getD_some, pairOccurrence, hg, ite_false,
          Function.comp, Occurrence.point, Bool.and_eq_true, decide_eq_true_eq,
          Option.some.injEq, exists_eq_left', WithTop.coe_lt_coe, hlt, hge]
        tauto
  · have := hess j
    simp only [List.mem_filter, List.mem_finRange, true_and] at this
    simp only [Function.comp, Occurrence.point, Bool.and_eq_true, decide_eq_true_eq,
      WithTop.coe_lt_top, and_true, this, hlt]
    tauto

end Output

section Homology

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k] (degree : Fin m → ℕ)
  {grade : Fin m → ℤ} (D : Matrix (Fin m) (Fin m) k)

omit [DecidableEq k] in
/-- For monotone grades, support in grades `≤ a` is support in the prefix `stage grade a`. -/
theorem sublevelSupported_iff_prefixSupported (hgrade : Monotone grade) (a : ℤ)
    (x : Fin m → k) : SublevelSupported grade a x ↔ PrefixSupported (stage grade a) x := by
  refine forall_congr' fun i => imp_congr_left ?_
  rw [← not_le, grade_le_iff_lt_stage hgrade, not_lt]

omit [DecidableEq k] in
/-- For monotone grades, the sublevel cycles in grades `≤ a` are the reducer's prefix cycles
`originalCycleSpace` at `stage grade a`. -/
theorem sublevelCycles_eq_originalCycleSpace (hgrade : Monotone grade) (p : ℕ) (a : ℤ) :
    sublevelCycles degree grade D p a = originalCycleSpace degree D p (stage grade a) := by
  ext x
  rw [mem_sublevelCycles, sublevelSupported_iff_prefixSupported hgrade]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

omit [DecidableEq k] in
/-- For monotone grades, the sublevel boundaries in grades `≤ a` are the reducer's prefix
boundaries `OriginalBoundary` at `stage grade a`. -/
theorem mem_sublevelBoundaries_iff_originalBoundary (hgrade : Monotone grade) (p : ℕ) (a : ℤ)
    (x : Fin m → k) :
    x ∈ sublevelBoundaries degree grade D p a ↔
      OriginalBoundary degree D p (stage grade a) x := by
  rw [mem_sublevelBoundaries]
  simp only [sublevelSupported_iff_prefixSupported hgrade]
  exact ⟨fun ⟨y, h1, h2, h3⟩ => ⟨y, h2, h1, h3⟩, fun ⟨y, h1, h2, h3⟩ => ⟨y, h2, h1, h3⟩⟩

variable {degree D}
variable {R V W : Matrix (Fin m) (Fin m) k} (hD2 : D * D = 0) (hR : R = D * V)
  (hcert : TraceChangeCertificate degree V W) (hRdegree : LowersDegree degree R)
  (hpiv : DistinctPivots R)

/-- Sublevel homology in grades `≤ a` is the reducer's prefix homology at `stage grade a`. -/
noncomputable def prefixHomologyEquiv (hgrade : Monotone grade) (p : ℕ) (a : ℤ) :
    sublevelHomology degree grade D p a ≃ₗ[k]
      originalHomology degree D R V W hD2 hR hcert hRdegree hpiv p (stage grade a) :=
  Submodule.Quotient.equiv _ _
    (LinearEquiv.ofEq _ _ (sublevelCycles_eq_originalCycleSpace degree D hgrade p a)) (by
      ext y
      rw [Submodule.mem_map_equiv, Submodule.mem_comap,
        originalHomology_kernel_eq_boundaries degree D R V W hD2 hR hcert hRdegree hpiv]
      exact mem_sublevelBoundaries_iff_originalBoundary degree D hgrade p a y.1)

/-- `prefixHomologyEquiv` keeps the representing cycle. -/
@[simp] theorem prefixHomologyEquiv_mk (hgrade : Monotone grade) (p : ℕ) (a : ℤ)
    (x : sublevelCycles degree grade D p a) :
    prefixHomologyEquiv hD2 hR hcert hRdegree hpiv hgrade p a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨x.1, (sublevelCycles_eq_originalCycleSpace degree D hgrade p a).le x.2⟩ :=
  rfl

/-- `prefixHomologyEquiv` is natural: it carries the sublevel structure map `a ≤ b` to the
reducer's prefix-homology map from `stage grade a` to `stage grade b`. -/
theorem prefixHomologyEquiv_naturality (hgrade : Monotone grade) (p : ℕ) {a b : ℤ}
    (hab : a ≤ b) :
    (prefixHomologyEquiv hD2 hR hcert hRdegree hpiv hgrade p b).toLinearMap ∘ₗ
        sublevelHomologyMap degree grade D p hab =
      originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p (stage grade a)
          (stage grade b) ∘ₗ
        (prefixHomologyEquiv hD2 hR hcert hRdegree hpiv hgrade p a).toLinearMap := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  apply (originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p
    (stage grade b)).injective
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe]
  rw [sublevelHomologyMap_mk, prefixHomologyEquiv_mk, prefixHomologyEquiv_mk,
    originalHomologyMap_mk degree D R V W hD2 hR hcert hRdegree hpiv p _ _
    (stage_mono grade hab)]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/-- The ranks of the sublevel structure maps are the ranks of the reducer's prefix-homology
maps. -/
theorem finrank_range_sublevelHomologyMap_eq (hgrade : Monotone grade) (p : ℕ) {a b : ℤ}
    (hab : a ≤ b) :
    Module.finrank k (LinearMap.range (sublevelHomologyMap degree grade D p hab)) =
      Module.finrank k (LinearMap.range (originalHomologyMap degree D R V W hD2 hR hcert
        hRdegree hpiv p (stage grade a) (stage grade b))) := by
  have h := congrArg LinearMap.range
    (prefixHomologyEquiv_naturality hD2 hR hcert hRdegree hpiv hgrade p hab)
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range _)] at h
  rw [← h, LinearEquiv.finrank_map_eq]

end Homology

section Rank

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k] {degree : Fin m → ℕ}
  {grade : Fin m → ℤ} {D : Matrix (Fin m) (Fin m) k}

/-- **Rank semantics of the graded reducer output.** For a square-zero, strictly upper
triangular, degree-lowering matrix with monotone grades, the rank of the structure map `a ≤ b`
of the degree-`p` grade-sublevel homology module is the slice count of `diagram` at `a ≤ b`. -/
theorem rankOfStructureMap_eq_countP (hD2 : D * D = 0) (hstrict : StrictBoundary D)
    (hdegree : LowersDegree degree D) (hgrade : Monotone grade) (p : ℕ) {a b : ℤ}
    (hab : a ≤ b) :
    rankOfStructureMap (sublevelHomologyPModule degree grade D p) hab =
      (diagram degree grade D p).points.countP (fun q => q.1 ≤ a ∧ (b : WithTop ℤ) < q.2) := by
  have h := matrixReductionTrace_normalForm_input degree D hD2 hstrict hdegree
  rw [countP_diagram degree hgrade D p hab]
  change Module.finrank k (LinearMap.range (sublevelHomologyMap degree grade D p hab)) = _
  rw [finrank_range_sublevelHomologyMap_eq hD2 h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 hgrade p hab]
  exact matrixReductionTrace_originalHomologyMap_rank_formula degree D hD2 hstrict hdegree p _ _
    (stage_mono grade hab) (stage_le grade b)

/-- Under the same hypotheses, every point of `diagram` has birth strictly below death. -/
theorem diagram_isPositive (hD2 : D * D = 0) (hstrict : StrictBoundary D)
    (hdegree : LowersDegree degree D) (hgrade : Monotone grade) (p : ℕ) :
    (diagram degree grade D p).IsPositive := by
  have hR : StrictBoundary (reduced D) :=
    (matrixReductionTrace_normalForm_input degree D hD2 hstrict hdegree).2.2.2.1
  intro q hq
  dsimp only [diagram] at hq
  obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.mp hq
  have hmem : o ∈ occurrences degree grade D :=
    (List.mem_filter.mp (Multiset.mem_coe.mp ho)).1
  rcases List.mem_append.mp hmem with hf | he
  · obtain ⟨⟨i, j⟩, hij, hq⟩ := List.mem_filterMap.mp hf
    unfold pairOccurrence at hq
    split_ifs at hq with hne
    cases hq
    have hpiv := (mem_pivotPairs D i j).mp hij
    have hlt : i < j := hR i j (by
      simpa only [Matrix.col_apply] using ((columnPivot_some_iff _ i).mp hpiv).1)
    simpa [Occurrence.point] using lt_of_le_of_ne (hgrade hlt.le) hne
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    simp [Occurrence.point]

/-- **The diagram determined by the ranks.** Under the same hypotheses, a positive diagram whose
slice counts are the ranks of the degree-`p` grade-sublevel homology module is `diagram`. -/
theorem eq_diagram_of_rankCounts (hD2 : D * D = 0) (hstrict : StrictBoundary D)
    (hdegree : LowersDegree degree D) (hgrade : Monotone grade) {p : ℕ} {E : Diagram ℤ}
    (hE : E.IsPositive)
    (h : ∀ (a b : ℤ) (hab : a ≤ b),
      E.points.countP (fun q => q.1 ≤ a ∧ (b : WithTop ℤ) < q.2) =
        rankOfStructureMap (sublevelHomologyPModule degree grade D p) hab) :
    E = diagram degree grade D p :=
  Diagram.eq_of_sliceCounts_eq hE (diagram_isPositive hD2 hstrict hdegree hgrade p)
    fun a b hab =>
      (h a b hab).trans (rankOfStructureMap_eq_countP hD2 hstrict hdegree hgrade p hab)

end Rank

section ReducerOrder

variable {ι : Type} [LinearOrder ι] [Fintype ι] {k : Type*} [Field k] [DecidableEq k]
  (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k)

/-- The occurrences of the reducer run on a filtered based complex in its reducer order. -/
def reducerOccurrences : List Occurrence :=
  occurrences (degree ∘ reducerEquiv degree grade) (grade ∘ reducerEquiv degree grade)
    (reducerMatrix degree grade D)

/-- The degree-`p` diagram of the reducer run on a filtered based complex in its reducer
order. -/
def reducerDiagram (p : ℕ) : Diagram ℤ :=
  diagram (degree ∘ reducerEquiv degree grade) (grade ∘ reducerEquiv degree grade)
    (reducerMatrix degree grade D) p

variable {degree grade D}

/-- **Rank semantics in the reducer order.** For a filtered differential over a field, the rank
of the structure map `a ≤ b` of its degree-`p` grade-sublevel homology module is the slice count
of `reducerDiagram` at `a ≤ b`. -/
theorem rankOfStructureMap_eq_countP_reducerDiagram
    (hD : IsFilteredDifferential degree grade D) (p : ℕ) {a b : ℤ} (hab : a ≤ b) :
    rankOfStructureMap (sublevelHomologyPModule degree grade D p) hab =
      (reducerDiagram degree grade D p).points.countP
        (fun q => q.1 ≤ a ∧ (b : WithTop ℤ) < q.2) :=
  (rankOfStructureMap_iso hab (reducerHomologyIso degree grade D p)).trans
    (rankOfStructureMap_eq_countP (reducerMatrix_sq_zero hD) (strictBoundary_reducerMatrix hD)
      (lowersDegree_reducerMatrix hD) (monotone_grade degree grade) p hab)

/-- For a filtered differential over a field, `reducerDiagram` is positive. -/
theorem reducerDiagram_isPositive (hD : IsFilteredDifferential degree grade D) (p : ℕ) :
    (reducerDiagram degree grade D p).IsPositive :=
  diagram_isPositive (reducerMatrix_sq_zero hD) (strictBoundary_reducerMatrix hD)
    (lowersDegree_reducerMatrix hD) (monotone_grade degree grade) p

/-- **The reducer diagram is the diagram of the ranks.** For a filtered differential over a
field, a positive diagram whose slice counts are the ranks of the degree-`p` grade-sublevel
homology module is `reducerDiagram`. -/
theorem eq_reducerDiagram_of_rankCounts (hD : IsFilteredDifferential degree grade D) {p : ℕ}
    {E : Diagram ℤ} (hE : E.IsPositive)
    (h : ∀ (a b : ℤ) (hab : a ≤ b),
      E.points.countP (fun q => q.1 ≤ a ∧ (b : WithTop ℤ) < q.2) =
        rankOfStructureMap (sublevelHomologyPModule degree grade D p) hab) :
    E = reducerDiagram degree grade D p :=
  Diagram.eq_of_sliceCounts_eq hE (reducerDiagram_isPositive hD p)
    fun a b hab => (h a b hab).trans (rankOfStructureMap_eq_countP_reducerDiagram hD p hab)

end ReducerOrder

end TDA.Persistence.Morse.ReducerDiagram
