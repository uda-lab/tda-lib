import TDA.Persistence.Reduction.SimplicialAdapterTemplate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.List.NodupEquivFin

/-! Finite, integer-graded simplex lists for ordinary unaugmented F₂ persistence. -/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration TDA.Persistence

abbrev Entry := Finset ℕ × ℤ
abbrev Input := List Entry

def faces (xs : Input) : List (Finset ℕ) := xs.map Prod.fst

/-- The five independent conditions on a list presentation. -/
def Valid (xs : Input) : Prop :=
  (∀ i : Fin xs.length, (xs.get i).1.Nonempty) ∧
  (faces xs).Nodup ∧
  (∀ i : Fin xs.length, ∀ t ∈ (xs.get i).1.powerset,
    t.Nonempty → t ∈ faces xs) ∧
  (∀ i j : Fin xs.length, (xs.get i).1 ⊂ (xs.get j).1 → i < j) ∧
  (∀ i j : Fin xs.length, i ≤ j → (xs.get i).2 ≤ (xs.get j).2)

/-- Every branch of the check is finite: list positions and finite powersets. -/
instance validDecidable (xs : Input) : Decidable (Valid xs) := by
  unfold Valid
  infer_instance

def validBool (xs : Input) : Bool := decide (Valid xs)

theorem validBool_iff (xs : Input) : validBool xs = true ↔ Valid xs := by
  simp [validBool]

/-- The represented complex has exactly the listed faces. -/
def complex (xs : Input) (h : Valid xs) : PreAbstractSimplicialComplex ℕ where
  faces := {s | s ∈ faces xs}
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    constructor
    · exact h.1 i
    · intro t hts ht
      exact h.2.2.1 i t (Finset.mem_powerset.mpr hts) ht

theorem mem_complex (xs : Input) (h : Valid xs) (s : Finset ℕ) :
    s ∈ complex xs h ↔ s ∈ faces xs := Iff.rfl

/-- List positions enumerate actual nonempty faces without a search oracle. -/
def listFace (xs : Input) (h : Valid xs) (i : Fin xs.length) :
    TotalFace (complex xs h) :=
  ⟨(xs.get i).1, by
    change (xs.get i).1 ∈ faces xs
    exact List.mem_map.mpr ⟨xs.get i, List.get_mem xs i, rfl⟩⟩

theorem listFace_bijective (xs : Input) (h : Valid xs) :
    Function.Bijective (listFace xs h) := by
  constructor
  · intro i j hij
    have hi : i.val < (faces xs).length := by simpa [faces] using i.isLt
    have hj : j.val < (faces xs).length := by simpa [faces] using j.isLt
    have heq : (faces xs)[i.val]'hi = (faces xs)[j.val]'hj := by
      simpa [faces, listFace] using congrArg Subtype.val hij
    exact Fin.ext ((h.2.1.getElem_inj_iff).mp heq)
  · intro s
    obtain ⟨a, ha, hs⟩ := List.mem_map.mp s.property
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hs

noncomputable def listEquiv (xs : Input) (h : Valid xs) :
    Fin xs.length ≃ TotalFace (complex xs h) :=
  Equiv.ofBijective (listFace xs h) (listFace_bijective xs h)

noncomputable def faceFintype (xs : Input) (h : Valid xs) :
    Fintype (TotalFace (complex xs h)) :=
  Fintype.ofEquiv (Fin xs.length) (listEquiv xs h)

theorem faceCount_eq_length (xs : Input) (h : Valid xs) :
    @faceCount ℕ (complex xs h) (faceFintype xs h) = xs.length := by
  letI := faceFintype xs h
  simpa using Fintype.card_congr (listEquiv xs h).symm

/-- The semantic filter reads the grade at the unique list position of a face. -/
noncomputable def gradeFilter (xs : Input) (h : Valid xs) :
    FilterFunction (complex xs h) ℤ where
  value s := (xs.get ((listEquiv xs h).symm s)).2
  mono := by
    intro s t hst
    let i := (listEquiv xs h).symm s
    let j := (listEquiv xs h).symm t
    have hs : (xs.get i).1 = s.val := by
      have he : listFace xs h i = s := (listEquiv xs h).apply_symm_apply s
      exact congrArg Subtype.val he
    have ht : (xs.get j).1 = t.val := by
      have he : listFace xs h j = t := (listEquiv xs h).apply_symm_apply t
      exact congrArg Subtype.val he
    have hij : i ≤ j := by
      by_cases heq : s.val = t.val
      · have : s = t := Subtype.ext heq
        simpa [i, j, this]
      · exact le_of_lt (h.2.2.2.1 i j (by
          rw [hs, ht]
          exact Finset.ssubset_iff_subset_ne.mpr ⟨hst, heq⟩))
    exact h.2.2.2.2 i j hij

/-- Cast list positions to the cardinality of the actual face type. -/
noncomputable def positionEquiv (xs : Input) (h : Valid xs) :
    Fin (@faceCount ℕ (complex xs h) (faceFintype xs h)) ≃
      TotalFace (complex xs h) :=
  (finCongr (faceCount_eq_length xs h)).trans (listEquiv xs h)

/-- The input order is itself a compatible actual-face enumeration. -/
noncomputable def compatibleOrder (xs : Input) (h : Valid xs) :
    letI := faceFintype xs h
    CompatibleOrder (gradeFilter xs h) := by
  letI := faceFintype xs h
  refine ⟨positionEquiv xs h, ?_, ?_⟩
  · intro i j hface
    let a := (Fin.cast (faceCount_eq_length xs h)) i
    let b := (Fin.cast (faceCount_eq_length xs h)) j
    have ha : (xs.get a).1 = ((positionEquiv xs h) i).val := by
      simp only [a, positionEquiv, Equiv.trans_apply, finCongr_apply,
        listEquiv, Equiv.ofBijective_apply, listFace]
    have hb : (xs.get b).1 = ((positionEquiv xs h) j).val := by
      simp only [b, positionEquiv, Equiv.trans_apply, finCongr_apply,
        listEquiv, Equiv.ofBijective_apply, listFace]
    have hab : a < b := h.2.2.2.1 a b (by simpa only [ha, hb] using hface)
    exact hab
  · intro i j hij
    have hcast : (Fin.cast (faceCount_eq_length xs h)) i ≤
        (Fin.cast (faceCount_eq_length xs h)) j := hij
    simpa only [Function.comp_apply, gradeFilter, positionEquiv,
      Equiv.trans_apply, finCongr_apply, listEquiv, Equiv.symm_apply_apply] using
      h.2.2.2.2 _ _ hcast

/-- Signed canonical deletions, evaluated over F₂ directly from list positions. -/
def boundary (xs : Input) : Matrix (Fin xs.length) (Fin xs.length) (ZMod 2) :=
  fun i j =>
    let s := (xs.get i).1
    let t := (xs.get j).1
    if hc : t.card = (s.card - 1) + 2 then
      ∑ a : Fin (s.card - 1 + 2),
        if t.erase (t.orderEmbOfFin hc a) = s then
          (-1 : ZMod 2) ^ (a : ℕ) else 0
    else 0

theorem positionEquiv_val (xs : Input) (h : Valid xs)
    (i : Fin (@faceCount ℕ (complex xs h) (faceFintype xs h))) :
    ((positionEquiv xs h) i).val =
      (xs.get (Fin.cast (faceCount_eq_length xs h) i)).1 := by
  simp only [positionEquiv, Equiv.trans_apply, finCongr_apply,
    listEquiv, Equiv.ofBijective_apply, listFace]

/-- The finite deletion computation is the actual signed simplicial boundary. -/
theorem boundary_eq_actual (xs : Input) (h : Valid xs) :
    letI := faceFintype xs h
    ∀ i j : Fin (faceCount (complex xs h)),
      boundary xs (Fin.cast (faceCount_eq_length xs h) i)
        (Fin.cast (faceCount_eq_length xs h) j) =
        actualBoundaryMatrix (ZMod 2) (compatibleOrder xs h) i j := by
  letI := faceFintype xs h
  intro i j
  let a := Fin.cast (faceCount_eq_length xs h) i
  let b := Fin.cast (faceCount_eq_length xs h) j
  have hia := positionEquiv_val xs h i
  have hjb := positionEquiv_val xs h j
  change ((compatibleOrder xs h).enum i).val =
    (xs.get (Fin.cast (faceCount_eq_length xs h) i)).1 at hia
  change ((compatibleOrder xs h).enum j).val =
    (xs.get (Fin.cast (faceCount_eq_length xs h) j)).1 at hjb
  have hipos : 0 < (xs.get a).1.card :=
    Finset.card_pos.mpr (h.1 a)
  have hd : ((xs.get b).1.card = ((xs.get a).1.card - 1) + 2) ↔
      faceDegree (compatibleOrder xs h) j =
        faceDegree (compatibleOrder xs h) i + 1 := by
    simp only [faceDegree]
    rw [show ((compatibleOrder xs h).enum i).val = (xs.get a).1 from hia,
      show ((compatibleOrder xs h).enum j).val = (xs.get b).1 from hjb]
    omega
  rw [actualBoundaryMatrix_apply]
  by_cases hc : (xs.get b).1.card = ((xs.get a).1.card - 1) + 2
  · have hg := hd.mp hc
    have hc' : (xs.get (Fin.cast (faceCount_eq_length xs h) j)).1.card =
        (xs.get (Fin.cast (faceCount_eq_length xs h) i)).1.card - 1 + 2 := hc
    simp only [boundary, dif_pos hc', dif_pos hg]
    simp only [deletedFace, indexedFace, faceDegree, hia, hjb]
    congr 1
    ext x
    congr 1
    apply propext
    constructor
    · intro he
      apply Subtype.ext
      convert he using 1
      congr 1
    · intro he
      have hv := congrArg Subtype.val he
      convert hv using 1
      congr 1
  · have hg : ¬ faceDegree (compatibleOrder xs h) j =
        faceDegree (compatibleOrder xs h) i + 1 := fun q => hc (hd.mpr q)
    have hc' : ¬ (xs.get (Fin.cast (faceCount_eq_length xs h) j)).1.card =
        (xs.get (Fin.cast (faceCount_eq_length xs h) i)).1.card - 1 + 2 := hc
    simp only [boundary, dif_neg hc', dif_neg hg]

theorem boundary_reindex (xs : Input) (h : Valid xs) :
    letI := faceFintype xs h
    boundary xs =
      (Matrix.reindex (finCongr (faceCount_eq_length xs h))
        (finCongr (faceCount_eq_length xs h)))
        (actualBoundaryMatrix (ZMod 2) (compatibleOrder xs h)) := by
  letI := faceFintype xs h
  apply Matrix.ext
  intro i j
  let a := (finCongr (faceCount_eq_length xs h)).symm i
  let b := (finCongr (faceCount_eq_length xs h)).symm j
  have he := boundary_eq_actual xs h a b
  simpa [Matrix.reindex_apply, a, b] using he

def degree (xs : Input) (i : Fin xs.length) : ℕ :=
  (xs.get i).1.card - 1

theorem degree_eq_faceDegree (xs : Input) (h : Valid xs)
    (i : Fin xs.length) :
    letI := faceFintype xs h
    degree xs i = faceDegree (compatibleOrder xs h)
      ((finCongr (faceCount_eq_length xs h)).symm i) := by
  letI := faceFintype xs h
  simp only [degree, faceDegree]
  have hv := positionEquiv_val xs h
    ((finCongr (faceCount_eq_length xs h)).symm i)
  change ((compatibleOrder xs h).enum
    ((finCongr (faceCount_eq_length xs h)).symm i)).val = _ at hv
  simpa using congrArg (fun s : Finset ℕ => s.card - 1) hv.symm

theorem boundary_sq_zero (xs : Input) (h : Valid xs) :
    boundary xs * boundary xs = 0 := by
  letI := faceFintype xs h
  let e := finCongr (faceCount_eq_length xs h)
  rw [boundary_reindex xs h]
  change (Matrix.reindexRingEquiv (ZMod 2) e)
      (actualBoundaryMatrix (ZMod 2) (compatibleOrder xs h)) *
    (Matrix.reindexRingEquiv (ZMod 2) e)
      (actualBoundaryMatrix (ZMod 2) (compatibleOrder xs h)) = 0
  rw [← map_mul]
  rw [actualBoundaryMatrix_sq_zero]
  exact map_zero _

theorem boundary_strict (xs : Input) (h : Valid xs) :
    StrictBoundary (boundary xs) := by
  letI := faceFintype xs h
  intro i j hij
  let e := finCongr (faceCount_eq_length xs h)
  have ha : actualBoundaryMatrix (ZMod 2) (compatibleOrder xs h)
      (e.symm i) (e.symm j) ≠ 0 := by
    simpa [boundary_reindex xs h, Matrix.reindex_apply, e] using hij
  have hs := actualBoundaryMatrix_strict (ZMod 2) (compatibleOrder xs h)
    (e.symm i) (e.symm j) ha
  exact hs

theorem boundary_lowersDegree (xs : Input) (h : Valid xs) :
    LowersDegree (degree xs) (boundary xs) := by
  letI := faceFintype xs h
  intro i j hij
  let e := finCongr (faceCount_eq_length xs h)
  have ha : actualBoundaryMatrix (ZMod 2) (compatibleOrder xs h)
      (e.symm i) (e.symm j) ≠ 0 := by
    simpa [boundary_reindex xs h, Matrix.reindex_apply, e] using hij
  have hd := actualBoundaryMatrix_lowersDegree (ZMod 2) (compatibleOrder xs h)
    (e.symm i) (e.symm j) ha
  simpa [degree_eq_faceDegree xs h, e] using hd

theorem boundary_vertex (xs : Input) (j : Fin xs.length)
    (hj : (xs.get j).1.card = 1) : (boundary xs).col j = 0 := by
  ext i
  simp only [Matrix.col_apply, Pi.zero_apply, boundary]
  split_ifs with hc
  · omega
  · rfl

/-- Replay the existing chronological reducer; the executed path uses no semantic choices. -/
def trace (xs : Input) : List (EarlierColumnOp xs.length (ZMod 2)) :=
  matrixReductionTrace (boundary xs)

def reduced (xs : Input) : Matrix (Fin xs.length) (Fin xs.length) (ZMod 2) :=
  replay (boundary xs) (trace xs)

private theorem reduce_reindex_cast {m n : ℕ} (h : m = n)
    (M : Matrix (Fin m) (Fin m) (ZMod 2)) :
    replay ((Matrix.reindex (finCongr h) (finCongr h)) M)
      (matrixReductionTrace ((Matrix.reindex (finCongr h) (finCongr h)) M)) =
    (Matrix.reindex (finCongr h) (finCongr h))
      (replay M (matrixReductionTrace M)) := by
  cases h
  rfl

theorem reduced_reindex (xs : Input) (h : Valid xs) :
    letI := faceFintype xs h
    reduced xs =
      (Matrix.reindex (finCongr (faceCount_eq_length xs h))
        (finCongr (faceCount_eq_length xs h)))
        (actualReducedBoundary (ZMod 2) (compatibleOrder xs h)) := by
  letI := faceFintype xs h
  have hD := boundary_reindex xs h
  simp only [reduced, trace, actualReducedBoundary]
  rw [hD]
  exact reduce_reindex_cast (faceCount_eq_length xs h) _

/-- One pair per nonzero reduced column, including pivot row zero. -/
def pivotPairs (xs : Input) : List (Fin xs.length × Fin xs.length) :=
  let R := reduced xs
  (List.finRange xs.length).filterMap fun j =>
    (columnPivot (R.col j)).map fun i => (i, j)

/-- Exactly the zero columns outside the image of all reduced pivots. -/
def essentialIndices (xs : Input) : List (Fin xs.length) :=
  let R := reduced xs
  let pairs := pivotPairs xs
  (List.finRange xs.length).filter fun i =>
    (columnPivot (R.col i)).isNone &&
      !pairs.any (fun q => q.1 == i)

theorem pivotPairs_nodup (xs : Input) : (pivotPairs xs).Nodup := by
  unfold pivotPairs
  apply List.Nodup.filterMap (l := List.finRange xs.length) ?_ (List.nodup_finRange _)
  intro j j' pair hj hj'
  rcases pair with ⟨i, k⟩
  simp only [Option.mem_def] at hj hj'
  cases h : columnPivot ((reduced xs).col j) <;>
    simp [h] at hj
  cases h' : columnPivot ((reduced xs).col j') <;>
    simp [h'] at hj'
  exact hj.2.trans hj'.2.symm

theorem pivotPairs_mem (xs : Input) (i j : Fin xs.length) :
    (i, j) ∈ pivotPairs xs ↔ columnPivot ((reduced xs).col j) = some i := by
  unfold pivotPairs
  simp only [List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨k, hk⟩
    cases h : columnPivot ((reduced xs).col k) with
    | none => simp [h] at hk
    | some p =>
        simp only [h, Option.map_some, Option.some.injEq] at hk
        have hp := (Prod.mk.inj hk).1
        have hj := (Prod.mk.inj hk).2
        subst p
        subst k
        exact h
  · intro hj
    exact ⟨j, by simp [hj]⟩

theorem essentialIndices_mem (xs : Input) (i : Fin xs.length) :
    i ∈ essentialIndices xs ↔ IsEssential (reduced xs) i := by
  simp only [essentialIndices, List.mem_filter, List.mem_finRange, true_and]
  simp only [IsEssential, IsPivot]
  constructor
  · intro hi
    have hz : columnPivot ((reduced xs).col i) = none := by
      cases hp : columnPivot ((reduced xs).col i) <;> simp [hp] at hi ⊢
    refine ⟨hz, ?_⟩
    intro ⟨j, hj⟩
    have ha : (pivotPairs xs).any (fun q => q.1 == i) = true := by
      simp only [List.any_eq_true, List.mem_finRange, true_and]
      exact ⟨(i, j), (pivotPairs_mem xs i j).mpr hj, by simp⟩
    simp [ha] at hi
  · rintro ⟨hz, hn⟩
    have hno : (pivotPairs xs).any (fun q => q.1 == i) = false := by
      cases ha : (pivotPairs xs).any (fun q => q.1 == i) with
      | false => rfl
      | true =>
          have hex : ∃ j : Fin xs.length,
              columnPivot ((reduced xs).col j) = some i := by
            obtain ⟨⟨r, j⟩, hp, hr⟩ := List.any_eq_true.mp ha
            have hri : r = i := by simpa using hr
            subst r
            exact ⟨j, (pivotPairs_mem xs i j).mp hp⟩
          exact (hn hex).elim
    simp [hz, hno]

theorem pivotPairs_eq_pivotIndexPairs (xs : Input) (p : ℕ) :
    ((pivotPairs xs).filter (fun q => degree xs q.1 = p) :
      Multiset (Fin xs.length × Fin xs.length)) =
      pivotIndexPairs (degree xs) (reduced xs) p := by
  have hpiv : DistinctPivots (reduced xs) := by
    intro i j q hi hj
    exact matrixReductionTrace_pivots_distinct (boundary xs) i j q hi hj
  apply (Multiset.Nodup.ext
    (Multiset.coe_nodup.mpr ((pivotPairs_nodup xs).filter _))
    (pivotIndexPairs_nodup (degree xs) (reduced xs) p)).2
  rintro ⟨i, j⟩
  simp only [List.mem_filter, Multiset.mem_coe, decide_eq_true_eq,
    pivotPairs_mem, mem_pivotIndexPairs_iff (degree xs) (reduced xs) hpiv]
  tauto

theorem essentialIndices_eq_pivotEssentialIndices (xs : Input) (p : ℕ) :
    ((essentialIndices xs).filter (fun i => degree xs i = p) :
      Multiset (Fin xs.length)) =
      pivotEssentialIndices (degree xs) (reduced xs) p := by
  have hn : (essentialIndices xs).Nodup :=
    (List.nodup_finRange xs.length).filter _
  apply (Multiset.Nodup.ext (Multiset.coe_nodup.mpr (hn.filter _))
    (pivotEssentialIndices_nodup (degree xs) (reduced xs) p)).2
  intro i
  simp only [List.mem_filter, Multiset.mem_coe, decide_eq_true_eq, essentialIndices_mem,
    mem_pivotEssentialIndices_iff]

private theorem pairs_reindex_cast {m n : ℕ} (hn : m = n)
    (d : Fin m → ℕ) (R : Matrix (Fin m) (Fin m) (ZMod 2)) (p : ℕ) :
    pivotIndexPairs (fun i => d ((finCongr hn).symm i))
      ((Matrix.reindex (finCongr hn) (finCongr hn)) R) p =
    (pivotIndexPairs d R p).map
      (fun q => ((finCongr hn) q.1, (finCongr hn) q.2)) := by
  cases hn
  simp [Matrix.reindex_refl_refl]

private theorem essential_reindex_cast {m n : ℕ} (hn : m = n)
    (d : Fin m → ℕ) (R : Matrix (Fin m) (Fin m) (ZMod 2)) (p : ℕ) :
    pivotEssentialIndices (fun i => d ((finCongr hn).symm i))
      ((Matrix.reindex (finCongr hn) (finCongr hn)) R) p =
    (pivotEssentialIndices d R p).map (finCongr hn) := by
  cases hn
  simp [Matrix.reindex_refl_refl]

theorem pivotPairs_semantic (xs : Input) (h : Valid xs) (p : ℕ) :
    letI := faceFintype xs h
    ((pivotPairs xs).filter (fun q => degree xs q.1 = p) :
      Multiset (Fin xs.length × Fin xs.length)) =
    (pivotIndexPairs (faceDegree (compatibleOrder xs h))
      (actualReducedBoundary (ZMod 2) (compatibleOrder xs h)) p).map
      (fun q => ((finCongr (faceCount_eq_length xs h)) q.1,
        (finCongr (faceCount_eq_length xs h)) q.2)) := by
  letI := faceFintype xs h
  let e := finCongr (faceCount_eq_length xs h)
  have hdeg : degree xs = fun i =>
      faceDegree (compatibleOrder xs h) (e.symm i) := by
    funext i
    exact degree_eq_faceDegree xs h i
  rw [pivotPairs_eq_pivotIndexPairs, hdeg, reduced_reindex xs h]
  exact pairs_reindex_cast (faceCount_eq_length xs h) _ _ p

theorem essentialIndices_semantic (xs : Input) (h : Valid xs) (p : ℕ) :
    letI := faceFintype xs h
    ((essentialIndices xs).filter (fun i => degree xs i = p) :
      Multiset (Fin xs.length)) =
    (pivotEssentialIndices (faceDegree (compatibleOrder xs h))
      (actualReducedBoundary (ZMod 2) (compatibleOrder xs h)) p).map
      (finCongr (faceCount_eq_length xs h)) := by
  letI := faceFintype xs h
  let e := finCongr (faceCount_eq_length xs h)
  have hdeg : degree xs = fun i =>
      faceDegree (compatibleOrder xs h) (e.symm i) := by
    funext i
    exact degree_eq_faceDegree xs h i
  rw [essentialIndices_eq_pivotEssentialIndices, hdeg, reduced_reindex xs h]
  exact essential_reindex_cast (faceCount_eq_length xs h) _ _ p

theorem grade_eq_semantic (xs : Input) (h : Valid xs)
    (i : Fin (@faceCount ℕ (complex xs h) (faceFintype xs h))) :
    letI := faceFintype xs h
    (xs.get ((finCongr (faceCount_eq_length xs h)) i)).2 =
      (gradeFilter xs h).value ((compatibleOrder xs h).enum i) := by
  letI := faceFintype xs h
  simp only [gradeFilter, compatibleOrder, positionEquiv,
    Equiv.trans_apply, finCongr_apply, Equiv.symm_trans_apply,
    Equiv.symm_apply_apply]

inductive Death where
  | finite (grade : ℤ)
  | essential
  deriving DecidableEq, Repr

structure Occurrence where
  degree : ℕ
  birth : ℤ
  death : Death
  deriving DecidableEq, Repr

def pairValue (xs : Input) (q : Fin xs.length × Fin xs.length) : ℤ × ℤ :=
  ((xs.get q.1).2, (xs.get q.2).2)

def pairOccurrence (xs : Input)
    (q : Fin xs.length × Fin xs.length) : Option Occurrence :=
  if (xs.get q.1).2 = (xs.get q.2).2 then none else
    some ⟨degree xs q.1, (xs.get q.1).2, .finite (xs.get q.2).2⟩

/-- Finite equal-grade index pairs vanish only at value-level extraction. -/
def finiteOccurrences (xs : Input) : List Occurrence :=
  (pivotPairs xs).filterMap (pairOccurrence xs)

def essentialOccurrences (xs : Input) : List Occurrence :=
  (essentialIndices xs).map fun i =>
    ⟨(xs.get i).1.card - 1, (xs.get i).2, .essential⟩

def occurrences (xs : Input) : List Occurrence :=
  finiteOccurrences xs ++ essentialOccurrences xs

def Occurrence.point (o : Occurrence) : ℤ × WithTop ℤ :=
  (o.birth, match o.death with
    | .finite d => d
    | .essential => ⊤)

theorem finiteOccurrences_offDiagonal (xs : Input) (o : Occurrence)
    (ho : o ∈ finiteOccurrences xs) :
    (o.birth : WithTop ℤ) ≠ (Occurrence.point o).2 := by
  unfold finiteOccurrences at ho
  obtain ⟨pair, _, hp⟩ := List.mem_filterMap.mp ho
  rcases pair with ⟨i, j⟩
  dsimp [pairOccurrence] at hp
  split_ifs at hp with he
  cases hp
  simpa [Occurrence.point] using he

private theorem finitePointsList (xs : Input) (p : ℕ)
    (pairs : List (Fin xs.length × Fin xs.length)) :
    ((pairs.filterMap (pairOccurrence xs)).filter (fun o => o.degree = p)).map
        Occurrence.point =
      (((pairs.filter (fun q => degree xs q.1 = p)).map (pairValue xs)).filter
        (fun q => q.1 ≠ q.2)).map
        (fun q => (q.1, (q.2 : WithTop ℤ))) := by
  induction pairs with
  | nil => rfl
  | cons q pairs ih =>
      rcases q with ⟨i, j⟩
      by_cases he : (xs.get i).2 = (xs.get j).2
      · have he' : xs[i.val].2 = xs[j.val].2 := he
        have hpair : pairOccurrence xs (i, j) = none := by
          simp [pairOccurrence, he']
        simp [List.filterMap_cons, List.filter_cons, List.map_cons,
          hpair, pairValue, he', ih]
        by_cases hp : degree xs i = p <;> simp [hp, pairValue, he']
      · by_cases hp : degree xs i = p
        · have he' : xs[i.val].2 ≠ xs[j.val].2 := he
          have hpair : pairOccurrence xs (i, j) =
              some ⟨degree xs i, (xs.get i).2, .finite (xs.get j).2⟩ := by
            simp [pairOccurrence, he']
          simp [List.filterMap_cons, List.filter_cons, List.map_cons,
            hpair, pairValue, he', hp, Occurrence.point, ih]
        · have he' : xs[i.val].2 ≠ xs[j.val].2 := he
          have hpair : pairOccurrence xs (i, j) =
              some ⟨degree xs i, (xs.get i).2, .finite (xs.get j).2⟩ := by
            simp [pairOccurrence, he']
          simp [List.filterMap_cons, List.filter_cons, List.map_cons,
            hpair, pairValue, he', hp, ih]

private theorem essentialPointsList (xs : Input) (p : ℕ)
    (indices : List (Fin xs.length)) :
    ((indices.map fun i =>
        (⟨degree xs i, (xs.get i).2, .essential⟩ : Occurrence)).filter
        (fun o => o.degree = p)).map Occurrence.point =
      (indices.filter (fun i => degree xs i = p)).map
        (fun i => ((xs.get i).2, (⊤ : WithTop ℤ))) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      by_cases hp : degree xs i = p
      · simp [List.filter_cons, List.map_cons, hp, Occurrence.point, ih]
        exact ih
      · simp [List.filter_cons, List.map_cons, hp, Occurrence.point, ih]
        exact ih

/-- Degreewise interpretation of all output records, retaining multiplicity. -/
def outputDiagram (xs : Input) (p : ℕ) : Diagram ℤ where
  points := (((occurrences xs).filter (fun o => o.degree = p) : List Occurrence) :
    Multiset Occurrence).map Occurrence.point
  offDiagonal := by
    intro q hq
    obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.mp hq
    have hh : o ∈ (occurrences xs).filter (fun o => o.degree = p) := ho
    have hmem : o ∈ occurrences xs := (List.mem_filter.mp hh).1
    rcases List.mem_append.mp hmem with hf | he
    · exact finiteOccurrences_offDiagonal xs o hf
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      simp [Occurrence.point]

theorem outputPointsList (xs : Input) (p : ℕ) :
    ((occurrences xs).filter (fun o => o.degree = p)).map Occurrence.point =
      (((pivotPairs xs).filter (fun q => degree xs q.1 = p)).map
        (pairValue xs) |>.filter (fun q => q.1 ≠ q.2)).map
        (fun q => (q.1, (q.2 : WithTop ℤ))) ++
      ((essentialIndices xs).filter (fun i => degree xs i = p)).map
        (fun i => ((xs.get i).2, (⊤ : WithTop ℤ))) := by
  simp only [occurrences, List.filter_append, List.map_append,
    finiteOccurrences, essentialOccurrences]
  rw [finitePointsList xs p (pivotPairs xs)]
  congr 1
  simpa only [degree] using essentialPointsList xs p (essentialIndices xs)

def pairValuesAtDegree (xs : Input) (p : ℕ) : Multiset (ℤ × ℤ) :=
  (((pivotPairs xs).filter (fun q => degree xs q.1 = p) :
    List (Fin xs.length × Fin xs.length)) : Multiset _).map (pairValue xs)

def essentialBirthsAtDegree (xs : Input) (p : ℕ) : Multiset ℤ :=
  (((essentialIndices xs).filter (fun i => degree xs i = p) :
    List (Fin xs.length)) : Multiset _).map (fun i => (xs.get i).2)

theorem outputDiagram_points (xs : Input) (p : ℕ) :
    (outputDiagram xs p).points =
      ((pairValuesAtDegree xs p).filter (fun q => q.1 ≠ q.2)).map
        (fun q => (q.1, (q.2 : WithTop ℤ))) +
      (essentialBirthsAtDegree xs p).map
        (fun b => (b, (⊤ : WithTop ℤ))) := by
  change (((occurrences xs).filter (fun o => o.degree = p)).map
    Occurrence.point : Multiset (ℤ × WithTop ℤ)) = _
  rw [outputPointsList]
  simp [pairValuesAtDegree, essentialBirthsAtDegree, List.map_map]
  simp [Function.comp_def]

theorem pairValuesAtDegree_semantic (xs : Input) (h : Valid xs) (p : ℕ) :
    letI := faceFintype xs h
    pairValuesAtDegree xs p =
      (pivotIndexPairs (faceDegree (compatibleOrder xs h))
        (actualReducedBoundary (ZMod 2) (compatibleOrder xs h)) p).map
        (pairValues (gradeFilter xs h) (compatibleOrder xs h)) := by
  letI := faceFintype xs h
  unfold pairValuesAtDegree
  rw [pivotPairs_semantic xs h p, Multiset.map_map]
  congr 1
  funext q
  rcases q with ⟨i, j⟩
  simp only [Function.comp_def, pairValue, pairValues]
  rw [grade_eq_semantic xs h i, grade_eq_semantic xs h j]

theorem essentialBirthsAtDegree_semantic (xs : Input) (h : Valid xs) (p : ℕ) :
    letI := faceFintype xs h
    essentialBirthsAtDegree xs p =
      (pivotEssentialIndices (faceDegree (compatibleOrder xs h))
        (actualReducedBoundary (ZMod 2) (compatibleOrder xs h)) p).map
        (birthValue (gradeFilter xs h) (compatibleOrder xs h)) := by
  letI := faceFintype xs h
  unfold essentialBirthsAtDegree
  rw [essentialIndices_semantic xs h p, Multiset.map_map]
  congr 1
  funext i
  simp only [Function.comp_def, birthValue]
  exact grade_eq_semantic xs h i

/-- The records produced by the finite computation are the actual sublevel
diagram occurrences in every degree, including the constant essential tail. -/
theorem outputDiagram_eq_dgm (xs : Input) (h : Valid xs) (p : ℕ) :
    letI := faceFintype xs h
    outputDiagram xs p = dgm (ZMod 2) (gradeFilter xs h) p := by
  letI := faceFintype xs h
  calc
    outputDiagram xs p = evaluatePivotTemplate (ZMod 2)
        (compatibleOrder xs h) (gradeFilter xs h)
        (compatibleOrder xs h).monotone p := by
      apply Diagram.ext
      rw [outputDiagram_points, pairValuesAtDegree_semantic xs h p,
        essentialBirthsAtDegree_semantic xs h p]
      rfl
    _ = dgm (ZMod 2) (gradeFilter xs h) p :=
      evaluatePivotTemplate_eq_dgm (ZMod 2) (compatibleOrder xs h)
        (gradeFilter xs h) (compatibleOrder xs h).monotone p

/-- A retained finite record has strictly ordered grade endpoints. -/
theorem finite_birth_lt_death (xs : Input) (h : Valid xs)
    (o : Occurrence) (ho : o ∈ occurrences xs) (d : ℤ)
    (hd : o.death = .finite d) : o.birth < d := by
  rcases List.mem_append.mp ho with ho | ho
  · unfold finiteOccurrences at ho
    obtain ⟨⟨i, j⟩, hpair, hp⟩ := List.mem_filterMap.mp ho
    have hpiv : columnPivot ((reduced xs).col j) = some i :=
      (pivotPairs_mem xs i j).mp hpair
    have hstrict : StrictBoundary (reduced xs) :=
      (matrixReductionTrace_normalForm_input (degree xs) (boundary xs)
        (boundary_sq_zero xs h) (boundary_strict xs h)
        (boundary_lowersDegree xs h)).2.2.2.1
    have hentry : reduced xs i j ≠ 0 := by
      simpa only [Matrix.col_apply] using
        ((columnPivot_some_iff ((reduced xs).col j) i).mp hpiv).1
    have hij : i < j := hstrict i j hentry
    have hle : (xs.get i).2 ≤ (xs.get j).2 := h.2.2.2.2 i j hij.le
    simp [pairOccurrence] at hp
    obtain ⟨hne, hocc⟩ := hp
    subst o
    cases hd
    exact lt_of_le_of_ne hle hne
  · obtain ⟨i, _, hp⟩ := List.mem_map.mp ho
    cases hp
    cases hd

/-- Invalid presentations have no certified result and are never repaired. -/
def run (xs : Input) : Option (List Occurrence) :=
  if validBool xs then some (occurrences xs) else none

theorem run_isSome_iff (xs : Input) : (run xs).isSome = true ↔ Valid xs := by
  simp [run, validBool_iff]

theorem run_eq_some_iff (xs : Input) (out : List Occurrence) :
    run xs = some out ↔ Valid xs ∧ out = occurrences xs := by
  cases hb : validBool xs with
  | false =>
      have hn : ¬ Valid xs := by
        intro h
        have ht := (validBool_iff xs).mpr h
        simp [hb] at ht
      simp [run, hb, hn]
  | true =>
      have hv : Valid xs := (validBool_iff xs).mp hb
      simp only [run, hb, ↓reduceIte, Option.some.injEq, hv, true_and]
      exact eq_comm

theorem run_eq_none_iff (xs : Input) : run xs = none ↔ ¬ Valid xs := by
  cases hb : validBool xs with
  | false =>
      have hn : ¬ Valid xs := by
        intro h
        have ht := (validBool_iff xs).mpr h
        simp [hb] at ht
      simp [run, hb, hn]
  | true =>
      have hv : Valid xs := (validBool_iff xs).mp hb
      simp [run, hb, hv]

/-- Two presentations of the same graded complex have the same interpreted
diagram, even when their equal-grade face orders and index pairings differ. -/
private theorem dgm_eq_of_heq {K L : PreAbstractSimplicialComplex ℕ}
    (iK : Fintype (TotalFace K)) (iL : Fintype (TotalFace L))
    (hK : K = L) (f : FilterFunction K ℤ) (g : FilterFunction L ℤ)
    (hf : HEq f g) (p : ℕ) :
    @dgm ℕ _ (ZMod 2) _ ℤ _ K iK f p =
      @dgm ℕ _ (ZMod 2) _ ℤ _ L iL g p := by
  cases hK
  cases hf
  have he : iK = iL := Subsingleton.elim _ _
  cases he
  rfl

theorem outputDiagram_eq_of_same_graded_complex (xs ys : Input)
    (hx : Valid xs) (hy : Valid ys)
    (hK : complex xs hx = complex ys hy)
    (hf : HEq (gradeFilter xs hx) (gradeFilter ys hy)) (p : ℕ) :
    outputDiagram xs p = outputDiagram ys p := by
  have hleft := outputDiagram_eq_dgm xs hx p
  have hright := outputDiagram_eq_dgm ys hy p
  rw [hleft, hright]
  exact dgm_eq_of_heq (faceFintype xs hx) (faceFintype ys hy)
    hK (gradeFilter xs hx) (gradeFilter ys hy) hf p

end TDA.Persistence.Reduction.FiniteInput
