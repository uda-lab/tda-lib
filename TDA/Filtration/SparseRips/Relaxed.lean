import TDA.Filtration.Rips
import TDA.Filtration.SparseRips.Deletion
import TDA.Simplicial.Contiguity

/-!
# Relaxed complexes and the sparse inclusion filtration

Relaxed dissimilarity adds both vertex weights to the original distance, including
self-pairs. Closed active complexes retain vertices at their deletion times.
Taking their union over all earlier nonnegative scales gives an ordinary inclusion
filtration on the fixed ambient vertex type.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial

noncomputable section

variable {V : Type*} [MetricSpace V]

local instance relaxedDecidableEq : DecidableEq V := Classical.decEq V

/-- A dissimilarity, rather than a purported metric: self-distances are twice the weight. -/
def relaxedDistance (η : ℝ) (time : V → Option ℝ) (r : ℝ) (x y : V) : ℝ :=
  dist x y + weight η (time x) r + weight η (time y) r

@[simp] theorem relaxedDistance_self (η : ℝ) (time : V → Option ℝ) (r : ℝ) (x : V) :
    relaxedDistance η time r x x = 2 * weight η (time x) r := by
  simp [relaxedDistance]; ring

/-- Closed relaxed threshold complexes, extended by bottom at negative scales. -/
def relaxedComplex (η : ℝ) (time : V → Option ℝ) (r : ℝ) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ 0 ≤ r ∧
    ∀ x ∈ s, ∀ y ∈ s, relaxedDistance η time r x y ≤ r}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht, hs.2.1,
      fun x hx y hy => hs.2.2 x (hts hx) y (hts hy)⟩⟩

@[simp] theorem mem_relaxedComplex (η : ℝ) (time : V → Option ℝ) (r : ℝ) (s : Finset V) :
    s ∈ relaxedComplex η time r ↔ s.Nonempty ∧ 0 ≤ r ∧
      ∀ x ∈ s, ∀ y ∈ s, relaxedDistance η time r x y ≤ r := Iff.rfl

/-- The half-slope bound makes relaxed threshold complexes nested. -/
theorem relaxedComplex_mono {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (time : V → Option ℝ) (ht : ∀ x t, t ∈ time x → 0 ≤ t) :
    Monotone (relaxedComplex η time) := by
  intro r s hrs σ hσ
  refine ⟨hσ.1, hσ.2.1.trans hrs, ?_⟩
  intro x hx y hy
  have hxy := hσ.2.2 x hx y hy
  have hxw := (weight_increment hη hη' (time x) (ht x) hσ.2.1 hrs).2
  have hyw := (weight_increment hη hη' (time y) (ht y) hσ.2.1 hrs).2
  dsimp [relaxedDistance] at hxy ⊢
  linarith

/-- Relaxed complexes are bounded between two diameter-scale Rips complexes. -/
theorem rips_le_relaxedComplex {η r : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (hr : 0 ≤ r) (time : V → Option ℝ) :
    (Rips.filter inferInstance).sublevel ((1 - 2 * η) * r) ≤ relaxedComplex η time r := by
  intro σ hσ
  obtain ⟨hne, hdist⟩ := (Rips.mem_sublevel_iff _ _ _).mp hσ
  refine ⟨hne, hr, ?_⟩
  intro x hx y hy
  have hwx := weight_le hη hη' hr (time x)
  have hwy := weight_le hη hη' hr (time y)
  have hxy := hdist x hx y hy
  dsimp [relaxedDistance]
  nlinarith

theorem relaxedComplex_le_rips {η r : ℝ} (hη : 0 ≤ η) (time : V → Option ℝ) :
    relaxedComplex η time r ≤ (Rips.filter inferInstance).sublevel r := by
  intro σ hσ
  apply (Rips.mem_sublevel_iff _ _ _).mpr
  refine ⟨hσ.1, ?_⟩
  intro x hx y hy
  have hwx := weight_nonneg hη hσ.2.1 (time x)
  have hwy := weight_nonneg hη hσ.2.1 (time y)
  have hxy := hσ.2.2 x hx y hy
  dsimp [relaxedDistance] at hxy
  linarith

variable [Fintype V]

/-- Restrict the relaxed complex to vertices whose deletion time has not passed. -/
def closedActiveComplex (seed : V) (η r : ℝ) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ relaxedComplex η (deletionTime seed η) r ∧
    ∀ x ∈ s, ClosedActive (deletionTime seed η x) r}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1.1, fun t hts ht =>
      ⟨⟨ht, hs.1.2.1, fun x hx y hy => hs.1.2.2 x (hts hx) y (hts hy)⟩,
        fun x hx => hs.2 x (hts hx)⟩⟩

@[simp] theorem mem_closedActiveComplex (seed : V) (η r : ℝ) (s : Finset V) :
    s ∈ closedActiveComplex seed η r ↔
      s ∈ relaxedComplex η (deletionTime seed η) r ∧
        ∀ x ∈ s, ClosedActive (deletionTime seed η x) r := Iff.rfl

/-- The union of all closed active complexes up to the current scale. -/
def sparseComplex (seed : V) (η r : ℝ) : PreAbstractSimplicialComplex V where
  faces := {s | ∃ a, 0 ≤ a ∧ a ≤ r ∧ s ∈ closedActiveComplex seed η a}
  isRelLowerSet_faces := by
    rintro s ⟨a, ha, har, hs⟩
    exact ⟨hs.1.1, fun t hts ht =>
      ⟨a, ha, har, (closedActiveComplex seed η a).isRelLowerSet_faces hs |>.2 hts ht⟩⟩

@[simp] theorem mem_sparseComplex (seed : V) (η r : ℝ) (s : Finset V) :
    s ∈ sparseComplex seed η r ↔ ∃ a, 0 ≤ a ∧ a ≤ r ∧ s ∈ closedActiveComplex seed η a :=
  Iff.rfl

theorem sparseComplex_mono (seed : V) (η : ℝ) : Monotone (sparseComplex seed η) := by
  intro r s hrs σ
  rintro ⟨a, ha, har, hσ⟩
  exact ⟨a, ha, har.trans hrs, hσ⟩

/-- The sparse filtration uses actual face inclusions at all scales. -/
def sparseFiltration (seed : V) (η : ℝ) : SimplicialFiltration ℝ V where
  toFun := sparseComplex seed η
  monotone' := sparseComplex_mono seed η

theorem sparseComplex_eq_bot_of_neg (seed : V) (η : ℝ) {r : ℝ} (hr : r < 0) :
    sparseComplex seed η r = ⊥ := by
  apply le_antisymm _ bot_le
  intro s hs
  obtain ⟨a, ha, har, _⟩ := hs
  exact (not_le_of_gt hr (ha.trans har)).elim

theorem closedActiveComplex_le_sparseComplex (seed : V) (η : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    closedActiveComplex seed η r ≤ sparseComplex seed η r := by
  intro s hs
  exact ⟨r, hr, le_rfl, hs⟩

/-- The initial vertex survives at every nonnegative scale, including a singleton input. -/
theorem singleton_seed_mem_sparse (seed : V) (η : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ({seed} : Finset V) ∈ sparseFiltration seed η r := by
  apply closedActiveComplex_le_sparseComplex seed η hr
  refine ⟨⟨by simp, hr, ?_⟩, ?_⟩
  · intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst x; subst y
    simpa [relaxedDistance] using hr
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    simp

/-- A seed-free extension chooses an initial vertex when one exists and uses bottom on empty input. -/
def finiteSparseFiltration (η : ℝ) : SimplicialFiltration ℝ V := by
  classical
  exact if h : Nonempty V then sparseFiltration (Classical.choice h) η else ⊥

@[simp] theorem finiteSparseFiltration_of_isEmpty [IsEmpty V] (η : ℝ) :
    finiteSparseFiltration (V := V) η = ⊥ := by
  simp [finiteSparseFiltration]

theorem sparseComplex_le_relaxedComplex (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (r : ℝ) :
    sparseComplex seed η r ≤ relaxedComplex η (deletionTime seed η) r := by
  intro σ hσ
  obtain ⟨a, _, har, hσa⟩ := hσ
  exact relaxedComplex_mono hη.le (by linarith) (deletionTime seed η)
    (deletionTime_nonneg seed hη hη') har hσa.1

end

end TDA.Filtration.SparseRips
