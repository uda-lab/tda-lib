import TDA.Filtration.SparseRips.PairEntry
import TDA.Filtration.SparseRips.Sparsity
import TDA.Persistence.LogScaleDiagram

/-!
# Closed face entry and the finite sparse filter

The entry of a finite face is the maximum of its attained relaxed pair entries.
Its faces occur in the sparse carrier exactly when this maximum precedes every
vertex deletion time. Thus the same entry grades an actual finite filter on the
sparse carrier, including all ties and weighted self-pairs.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial TDA.Filtration TDA.Persistence

noncomputable section

variable {V : Type*} [MetricSpace V]

local instance faceEntryDecidableEq : DecidableEq V := Classical.decEq V

/-- Maximum attained relaxed entry over every pair, including self-pairs. -/
def faceEntry (η : ℝ) (time : V → Option ℝ) (σ : Finset V) : ℝ :=
  (σ ×ˢ σ).fold max 0 (fun p => pairEntry (η := η) time p.1 p.2)

theorem faceEntry_nonneg (η : ℝ) (time : V → Option ℝ) (σ : Finset V) :
    0 ≤ faceEntry η time σ := by
  exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

theorem pairEntry_le_faceEntry (η : ℝ) (time : V → Option ℝ)
    {σ : Finset V} {x y : V} (hx : x ∈ σ) (hy : y ∈ σ) :
    pairEntry (η := η) time x y ≤ faceEntry η time σ := by
  exact (Finset.le_fold_max _).mpr
    (Or.inr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, le_rfl⟩)

theorem faceEntry_le_iff {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 3)
    (time : V → Option ℝ) (ht : ∀ x t, t ∈ time x → 0 ≤ t)
    (σ : Finset V) {r : ℝ} (hr : 0 ≤ r) :
    faceEntry η time σ ≤ r ↔
      ∀ x ∈ σ, ∀ y ∈ σ, relaxedDistance η time r x y ≤ r := by
  classical
  unfold faceEntry
  rw [Finset.fold_max_le]
  constructor
  · intro h x hx y hy
    exact (pairEntry_le_iff hη hη' time ht x y hr).mp
      (h.2 (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩))
  · intro h
    refine ⟨hr, ?_⟩
    intro p hp
    exact (pairEntry_le_iff hη hη' time ht p.1 p.2 hr).mpr
      (h p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)

theorem faceEntry_mono (η : ℝ) (time : V → Option ℝ)
    {σ τ : Finset V} (hστ : σ ⊆ τ) :
    faceEntry η time σ ≤ faceEntry η time τ := by
  classical
  change (σ ×ˢ σ).fold max 0 (fun p => pairEntry (η := η) time p.1 p.2) ≤
    faceEntry η time τ
  apply (Finset.fold_max_le _).mpr
  refine ⟨faceEntry_nonneg η time τ, ?_⟩
  intro p hp
  exact pairEntry_le_faceEntry η time
    (hστ (Finset.mem_product.mp hp).1) (hστ (Finset.mem_product.mp hp).2)

theorem mem_relaxedComplex_iff_faceEntry {η : ℝ} (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 3) (time : V → Option ℝ)
    (ht : ∀ x t, t ∈ time x → 0 ≤ t) (σ : Finset V) (r : ℝ) :
    σ ∈ relaxedComplex η time r ↔
      σ.Nonempty ∧ 0 ≤ r ∧ faceEntry η time σ ≤ r := by
  rw [mem_relaxedComplex]
  constructor
  · rintro ⟨hne, hr, hp⟩
    exact ⟨hne, hr, (faceEntry_le_iff hη hη' time ht σ hr).mpr hp⟩
  · rintro ⟨hne, hr, hp⟩
    exact ⟨hne, hr, (faceEntry_le_iff hη hη' time ht σ hr).mp hp⟩

variable [Fintype V]

/-- On a sparse face, the first relaxed entry still precedes every deletion. -/
theorem mem_sparseCarrier_iff_faceEntry (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (σ : Finset V) :
    σ ∈ sparseCarrier seed η ↔
      σ.Nonempty ∧ ∀ x ∈ σ,
        ClosedActive (deletionTime seed η x)
          (faceEntry η (deletionTime seed η) σ) := by
  let time := deletionTime seed η
  have ht := deletionTime_nonneg seed hη hη'
  constructor
  · rintro ⟨a, ha, hσ⟩
    have hentry : faceEntry η time σ ≤ a :=
      ((mem_relaxedComplex_iff_faceEntry hη.le hη' time ht σ a).mp hσ.1).2.2
    refine ⟨hσ.1.1, ?_⟩
    intro x hx
    have hactive := hσ.2 x hx
    cases htx : time x with
    | none =>
        change ClosedActive (time x) (faceEntry η time σ)
        simp only [ClosedActive, htx, Option.elim_none]
    | some t =>
        change ClosedActive (time x) a at hactive
        change ClosedActive (time x) (faceEntry η time σ)
        simp only [ClosedActive, htx, Option.elim_some] at hactive ⊢
        exact hentry.trans hactive
  · rintro ⟨hne, hactive⟩
    let a := faceEntry η time σ
    have ha : 0 ≤ a := faceEntry_nonneg η time σ
    refine ⟨a, ha, ?_⟩
    constructor
    · exact (mem_relaxedComplex_iff_faceEntry hη.le hη' time ht σ a).mpr
        ⟨hne, ha, le_rfl⟩
    · exact hactive

/-- A face is present at scale `r` precisely when it belongs to the actual
sparse carrier and its attained entry is at most `r`. -/
theorem mem_sparseComplex_iff_faceEntry (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (σ : Finset V) (r : ℝ) :
    σ ∈ sparseComplex seed η r ↔
      σ ∈ sparseCarrier seed η ∧ faceEntry η (deletionTime seed η) σ ≤ r := by
  constructor
  · rintro ⟨a, ha, har, hσ⟩
    refine ⟨⟨a, ha, hσ⟩, ?_⟩
    have hentry := ((mem_relaxedComplex_iff_faceEntry hη.le hη'
      (deletionTime seed η) (deletionTime_nonneg seed hη hη') σ a).mp hσ.1).2.2
    exact hentry.trans har
  · rintro ⟨hcarrier, hentry⟩
    let a := faceEntry η (deletionTime seed η) σ
    have ha : 0 ≤ a := faceEntry_nonneg η (deletionTime seed η) σ
    refine ⟨a, ha, hentry, ?_⟩
    have hc := (mem_sparseCarrier_iff_faceEntry seed hη hη' σ).mp hcarrier
    exact ⟨(mem_relaxedComplex_iff_faceEntry hη.le hη'
      (deletionTime seed η) (deletionTime_nonneg seed hη hη') σ a).mpr
        ⟨hc.1, ha, le_rfl⟩, hc.2⟩

/-- The sparse carrier's finite face values are their actual first entry times. -/
def sparseFilter (seed : V) (η : ℝ) : FilterFunction (sparseCarrier seed η) ℝ where
  value σ := faceEntry η (deletionTime seed η) σ.val
  mono h := faceEntry_mono η (deletionTime seed η) h

theorem sparseFilter_sublevel_eq (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (r : ℝ) :
    (sparseFilter seed η).sublevel r = sparseComplex seed η r := by
  ext σ
  change (∃ hs : σ ∈ sparseCarrier seed η,
    faceEntry η (deletionTime seed η) σ ≤ r) ↔
      σ ∈ sparseComplex seed η r
  rw [mem_sparseComplex_iff_faceEntry seed hη hη' σ r]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, h₂⟩

/-- The constructed finite filter recovers the sparse inclusion filtration,
not merely its homology. -/
theorem sparseFilter_sublevelFiltration_eq (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) :
    (sparseFilter seed η).sublevelFiltration = sparseFiltration seed η := by
  apply OrderHom.ext
  funext r
  exact sparseFilter_sublevel_eq seed hη hη' r

/-- A finite vertex type has finitely many faces in the actual sparse carrier. -/
noncomputable instance sparseCarrierFintype (seed : V) (η : ℝ) :
    Fintype (TotalFace (sparseCarrier seed η)) :=
  Fintype.ofFinite _

/-- Every sparse edge enters at a strictly positive attained time. -/
theorem sparseFilter_positiveOnEdges [LinearOrder V] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) :
    PositiveOnEdges (sparseFilter seed η) := by
  intro σ hσ
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hσ
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  have hpair := dist_le_pairEntry hη.le hη' (deletionTime seed η)
    (deletionTime_nonneg seed hη hη') x y
  have hface := pairEntry_le_faceEntry η (deletionTime seed η) hx hy
  change 0 < faceEntry η (deletionTime seed η) σ.val
  exact hdist.trans_le (hpair.trans hface)

end

end TDA.Filtration.SparseRips
