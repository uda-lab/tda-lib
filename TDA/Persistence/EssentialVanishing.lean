import TDA.Simplicial.Cone
import TDA.Persistence.TotalPersistenceRipsCech
import TDA.Persistence.SublevelDiagramMonotone
import TDA.Persistence.CechPersistenceImage
import TDA.Persistence.RipsPersistenceImage

set_option autoImplicit false

/-!
# Essential bars on the full complex

This module counts essential bars, proves their vanishing in positive degree for every
filter on the full complex, and supplies the resulting size-uniform consumers.  The key
observation is that essential bars count the homology of the whole complex, so they vanish
in degree at least one on a full simplex for every filter.  Total persistence and kernel
embeddings already exclude essential bars, so the merged bounds from Issue #374 keep their
value.  No KFH18 statement beyond the bounds already proved in Issue #374 is claimed here.
-/

universe u w

namespace TDA.Persistence

open TDA.Simplicial TDA.Filtration CategoryTheory CategoryTheory.Limits

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TotalFace K)]
variable {α : Type w} [LinearOrder α]

/-- The essential part of a persistence multiset is exactly its top-death count. -/
theorem card_essentialPart_eq_countP {α} [LinearOrder α]
    (s : Multiset (α × WithTop α)) :
    (essentialPart s).card = s.countP (fun p => p.2 = ⊤) := by
  classical
  have h := congrArg
    (Multiset.countP (fun p : α × WithTop α => p.2 = ⊤))
    (parts_reconstruct s)
  simpa [Multiset.countP_add, Multiset.countP_map] using h

/-- Under a threshold containing every face value, essential bars have the rank of whole-complex
homology. -/
theorem card_essentialPart_dgm_eq_finrank (f : FilterFunction K α) (n : ℕ) (t : α)
    (ht : ∀ s, f.value s ≤ t) :
    (essentialPart (dgm k f n).points).card =
      Module.finrank k (simplicialHomology K k n) := by
  classical
  have hparts : ∀ p ∈ (dgm k f n).points,
      p ∈ (finitePart (dgm k f n).points).map
          (fun q => (q.1, (q.2 : WithTop α))) +
        (essentialPart (dgm k f n).points).map
          (fun b => (b, (⊤ : WithTop α))) := by
    intro p hp
    rw [parts_reconstruct]
    exact hp
  have hbirth : ∀ p ∈ (dgm k f n).points, p.1 ∈ f.criticalValues := by
    intro p hp
    rcases Multiset.mem_add.mp (hparts p hp) with hf | he
    · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hf
      exact (mem_criticalValues_of_mem_finitePart_dgm k f hq).1
    · obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp he
      exact mem_criticalValues_of_mem_essentialPart_dgm k f hb
  have hdeath_le : ∀ p ∈ (dgm k f n).points, p.2 ≠ ⊤ →
      p.2 ≤ (t : WithTop α) := by
    intro p hp htop
    rcases Multiset.mem_add.mp (hparts p hp) with hf | he
    · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hf
      obtain ⟨s, hs⟩ := (FilterFunction.mem_criticalValues f q.2).1
        (mem_criticalValues_of_mem_finitePart_dgm k f hq).2
      have hqle : q.2 ≤ t := by
        rw [← hs]
        exact ht s
      simpa using hqle
    · obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp he
      exact (htop rfl).elim
  have hcount :
      (dgm k f n).points.countP (fun p => p.2 = ⊤) =
        (dgm k f n).points.countP
          (fun p => p.1 ≤ t ∧ (t : WithTop α) < p.2) := by
    apply Multiset.countP_congr rfl
    intro p hp
    apply propext
    constructor
    · intro htop
      have hle : p.1 ≤ t := by
        obtain ⟨s, hs⟩ := (FilterFunction.mem_criticalValues f p.1).1
          (hbirth p hp)
        rw [← hs]
        exact ht s
      exact ⟨hle, by simp [htop]⟩
    · rintro ⟨_, hlt⟩
      by_contra htop
      exact (not_lt_of_ge (hdeath_le p hp htop)) hlt
  have hrank := finrank_sublevelHomology_eq_countP k f n t
  rw [FilterFunction.sublevel_eq_self_of_forall_le f t ht] at hrank
  calc
    (essentialPart (dgm k f n).points).card =
        (dgm k f n).points.countP (fun p => p.2 = ⊤) :=
      card_essentialPart_eq_countP _
    _ = (dgm k f n).points.countP
        (fun p => p.1 ≤ t ∧ (t : WithTop α) < p.2) := hcount
    _ = Module.finrank k (simplicialHomology K k n) := hrank.symm

/-- A zero whole-complex homology module has no essential bars. -/
theorem essentialPart_dgm_eq_zero_of_isZero (f : FilterFunction K α) {n : ℕ}
    (h : IsZero (simplicialHomology K k n)) :
    essentialPart (dgm k f n).points = 0 := by
  classical
  apply Multiset.eq_zero_of_forall_notMem
  intro b hb
  obtain ⟨s₀, hs₀⟩ :=
    (FilterFunction.mem_criticalValues f b).1
      (mem_criticalValues_of_mem_essentialPart_dgm k f hb)
  let t : α := Finset.univ.sup' ⟨s₀, Finset.mem_univ _⟩
    (fun s : TotalFace K => f.value s)
  have ht : ∀ s, f.value s ≤ t := by
    intro s
    exact Finset.le_sup' (fun q : TotalFace K => f.value q) (Finset.mem_univ s)
  have hcard := card_essentialPart_dgm_eq_finrank k f n t ht
  letI : Subsingleton (simplicialHomology K k n) :=
    ModuleCat.subsingleton_of_isZero h
  have hzero : Module.finrank k (simplicialHomology K k n) = 0 :=
    Module.finrank_zero_of_subsingleton (R := k)
  have hcard0 : (essentialPart (dgm k f n).points).card = 0 :=
    hcard.trans hzero
  have hpos : 0 < (essentialPart (dgm k f n).points).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩
  exact Nat.not_lt_zero _ (hcard0 ▸ hpos)

/-- Every positive-degree diagram on the full simplex has no essential bars. -/
theorem essentialPart_dgm_fullComplex_eq_zero [Fintype V]
    (f : FilterFunction (Rips.fullComplex V) α) {n : ℕ} (hn : 1 ≤ n) :
    essentialPart (dgm k f n).points = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
  apply essentialPart_dgm_eq_zero_of_isZero k f
  simpa only [Rips.fullComplex] using
    (TDA.Simplicial.isZero_simplicialHomology_top_succ
      (V := V) k m)

/-- A nonempty full simplex has exactly one degree-zero essential bar. -/
theorem card_essentialPart_dgm_fullComplex_zero [Fintype V] [Nonempty V]
    (f : FilterFunction (Rips.fullComplex V) α) :
    (essentialPart (dgm k f 0).points).card = 1 := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  let s₀ : TotalFace (Rips.fullComplex V) :=
    ⟨{v}, (Rips.mem_fullComplex_iff _).2 (by simp)⟩
  let t : α := Finset.univ.sup' ⟨s₀, Finset.mem_univ _⟩
    (fun s : TotalFace (Rips.fullComplex V) => f.value s)
  have ht : ∀ s, f.value s ≤ t := by
    intro s
    exact Finset.le_sup' (fun q : TotalFace (Rips.fullComplex V) => f.value q)
      (Finset.mem_univ s)
  calc
    (essentialPart (dgm k f 0).points).card =
        Module.finrank k (simplicialHomology (Rips.fullComplex V) k 0) :=
      card_essentialPart_dgm_eq_finrank k f 0 t ht
    _ = 1 := by
      exact TDA.Simplicial.finrank_simplicialHomology_top_zero (V := V) k

/-- In positive degree, a full-complex diagram is exactly its finite part. -/
theorem dgm_points_fullComplex_eq_finite [Fintype V]
    (f : FilterFunction (Rips.fullComplex V) α) {n : ℕ} (hn : 1 ≤ n) :
    (dgm k f n).points =
      (finitePart (dgm k f n).points).map
        (fun p => (p.1, (p.2 : WithTop α))) := by
  calc
    (dgm k f n).points =
        (finitePart (dgm k f n).points).map
            (fun p => (p.1, (p.2 : WithTop α))) +
          (essentialPart (dgm k f n).points).map
            (fun b => (b, (⊤ : WithTop α))) :=
      (parts_reconstruct (dgm k f n).points).symm
    _ = (finitePart (dgm k f n).points).map
        (fun p => (p.1, (p.2 : WithTop α))) := by
      rw [essentialPart_dgm_fullComplex_eq_zero k f hn]
      simp

namespace Rips

variable [Fintype V]

/-- Positive-degree Rips diagrams on the full simplex have no essential bars. -/
theorem essentialPart_dgm_eq_zero (d : MetricSpace V) {n : ℕ} (hn : 1 ≤ n) :
    essentialPart (dgm k (Rips.filter d) n).points = 0 :=
  essentialPart_dgm_fullComplex_eq_zero k (Rips.filter d) hn

/-- A nonempty Rips full simplex has one degree-zero essential bar. -/
theorem card_essentialPart_dgm_zero [Nonempty V] (d : MetricSpace V) :
    (essentialPart (dgm k (Rips.filter d) 0).points).card = 1 :=
  card_essentialPart_dgm_fullComplex_zero k (Rips.filter d)

omit [LinearOrder V] in
/-- A Rips sublevel at or above the full-carrier diameter is the full simplex. -/
theorem sublevel_eq_fullComplex (d : MetricSpace V) {r : ℝ}
    (hr : Rips.diameter d Finset.univ ≤ r) :
    (Rips.filter d).sublevel r = Rips.fullComplex V := by
  apply FilterFunction.sublevel_eq_self_of_forall_le
  intro s
  exact (Rips.filter_value_le_diameter_univ d s).trans hr

/-- A Rips sublevel above the full-carrier diameter has zero positive-degree homology. -/
theorem isZero_sublevelHomology_of_diameter_le
    (d : MetricSpace V) (R : Type*) [Ring R] {n : ℕ} {r : ℝ} (hn : 1 ≤ n)
    (hr : Rips.diameter d Finset.univ ≤ r) :
    IsZero (simplicialHomology ((Rips.filter d).sublevel r) R n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
  rw [Rips.sublevel_eq_fullComplex d hr]
  simpa only [Rips.fullComplex] using
    (TDA.Simplicial.isZero_simplicialHomology_top_succ
      (V := V) R m)

end Rips

namespace Cech

variable {X : Type*} [PseudoMetricSpace X] [Fintype V]

/-- Positive-degree Čech diagrams on the full simplex have no essential bars. -/
theorem essentialPart_dgm_eq_zero (p : V → X) {n : ℕ} (hn : 1 ≤ n) :
    essentialPart (dgm k (Cech.filter p) n).points = 0 :=
  essentialPart_dgm_fullComplex_eq_zero k (Cech.filter p) hn

/-- A nonempty Čech full simplex has one degree-zero essential bar. -/
theorem card_essentialPart_dgm_zero [Nonempty V] (p : V → X) :
    (essentialPart (dgm k (Cech.filter p) 0).points).card = 1 :=
  card_essentialPart_dgm_fullComplex_zero k (Cech.filter p)

omit [LinearOrder V] in
/-- A Čech sublevel at or above an enclosing radius is the full simplex. -/
theorem sublevel_eq_fullComplex (p : V → X) (x : X) {r : ℝ}
    (hr : Cech.radiusAt p x Finset.univ ≤ r) :
    (Cech.filter p).sublevel r = Rips.fullComplex V := by
  apply FilterFunction.sublevel_eq_self_of_forall_le
  intro s
  exact (Cech.filter_value_le_radiusAt p s x).trans
    ((Cech.radiusAt_mono p x (Finset.subset_univ _)).trans hr)

/-- A Čech sublevel above an enclosing radius has zero positive-degree homology. -/
theorem isZero_sublevelHomology_of_radiusAt_le
    (p : V → X) (x : X) (R : Type*) [Ring R] {n : ℕ} {r : ℝ} (hn : 1 ≤ n)
    (hr : Cech.radiusAt p x Finset.univ ≤ r) :
    IsZero (simplicialHomology ((Cech.filter p).sublevel r) R n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
  rw [Cech.sublevel_eq_fullComplex p x hr]
  simpa only [Rips.fullComplex] using
    (TDA.Simplicial.isZero_simplicialHomology_top_succ
      (V := V) R m)

end Cech

/-- The finite-occurrence count of a full-complex diagram is bounded by its face count. -/
theorem card_finiteOccurrences_dgm_fullComplex_le [Fintype V]
    (f : FilterFunction (Rips.fullComplex V) ℝ) (n : ℕ) :
    Fintype.card (dgm k f n).finiteOccurrences ≤
      Nat.choose (Fintype.card V) (n + 2) := by
  rw [Multiset.card_coe]
  calc
    (finitePart (dgm k f n).points).card ≤
        Nat.card (Face (Rips.fullComplex V) (n + 1)) :=
      card_finitePart_dgm_le k f n
    _ = Nat.choose (Fintype.card V) (n + 2) := by
      simpa [Nat.add_assoc] using card_face_fullComplex (V := V) (n + 1)

namespace Cech

variable {X : Type*} [PseudoMetricSpace X] [Fintype V]

/-- The Čech weighted-kernel bound with both finite counts replaced by the full-simplex count. -/
theorem norm_diagramEmbedding_sub_le_choose_mul_displacement
    (p q : V → X) (n : ℕ) (σ : ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm k (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding σ w (dgm k (Cech.filter q) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        (2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ)) * Cech.displacement p q := by
  have hbase := norm_diagramEmbedding_sub_le_displacement
    k p q n σ hA hB w
  have hpNat : Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences ≤
      Nat.choose (Fintype.card V) (n + 2) :=
    card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter p) n
  have hqNat : Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences ≤
      Nat.choose (Fintype.card V) (n + 2) :=
    card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter q) n
  have hp : (Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast hpNat
  have hq : (Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast hqNat
  have hcount :
      ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
        Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) ≤
        2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    calc
      ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
        Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) =
          (Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℝ) +
            (Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℝ) := by
              norm_num
      _ ≤ (Nat.choose (Fintype.card V) (n + 2) : ℝ) +
            (Nat.choose (Fintype.card V) (n + 2) : ℝ) := add_le_add hp hq
      _ = 2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by ring
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount
      (WeightedKernel.stabilityConstant_nonneg σ hA hB))
    (Cech.displacement_nonneg p q))

/-- The Čech persistence-image bound with both finite counts replaced by the full-simplex count. -/
theorem norm_finiteDiagramImage_sub_le_choose_mul_displacement
    (p q : V → X) (n : ℕ) {K : Type*} [Fintype K] {σ A B : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P (dgm k (Cech.filter p) n) -
        PersistenceImage.finiteDiagramImage σ w P (dgm k (Cech.filter q) n)‖ ≤
      PersistenceImage.stabilityConstant σ A B *
        (2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ)) * Cech.displacement p q := by
  have hbase := norm_finiteDiagramImage_sub_le_displacement
    k p q n hσ hA hB w P hm hd
  have hpNat := card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter p) n
  have hqNat := card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter q) n
  have hp : (Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast hpNat
  have hq : (Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast hqNat
  have hcount :
      ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
        Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) ≤
        2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    calc
      ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
        Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) =
          (Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℝ) +
            (Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℝ) := by
              norm_num
      _ ≤ (Nat.choose (Fintype.card V) (n + 2) : ℝ) +
            (Nat.choose (Fintype.card V) (n + 2) : ℝ) := add_le_add hp hq
      _ = 2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by ring
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount
      (PersistenceImage.stabilityConstant_nonneg hσ hA hB))
    (Cech.displacement_nonneg p q))

end Cech

namespace Rips

variable [Fintype V]

/-- The Rips persistence-image bound with both finite counts replaced by the full-simplex count. -/
theorem norm_finiteDiagramImage_sub_le_choose_mul_pairwiseDiscrepancy
    (d e : MetricSpace V) (n : ℕ) {K : Type*} [Fintype K] {σ A B : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P (dgm k (Rips.filter d) n) -
        PersistenceImage.finiteDiagramImage σ w P (dgm k (Rips.filter e) n)‖ ≤
      PersistenceImage.stabilityConstant σ A B *
        (2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ)) *
          Rips.pairwiseDiscrepancy d e := by
  have hbase := norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy
    k d e n hσ hA hB w P hm hd
  have hdNat := card_finiteOccurrences_dgm_fullComplex_le k (Rips.filter d) n
  have heNat := card_finiteOccurrences_dgm_fullComplex_le k (Rips.filter e) n
  have hd' : (Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast hdNat
  have he' : (Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℝ) ≤
      (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    exact_mod_cast heNat
  have hcount :
      ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
        Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) ≤
        2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by
    calc
      ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
        Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) =
          (Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences : ℝ) +
            (Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℝ) := by
              norm_num
      _ ≤ (Nat.choose (Fintype.card V) (n + 2) : ℝ) +
            (Nat.choose (Fintype.card V) (n + 2) : ℝ) := add_le_add hd' he'
      _ = 2 * (Nat.choose (Fintype.card V) (n + 2) : ℝ) := by ring
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount
      (PersistenceImage.stabilityConstant_nonneg hσ hA hB))
    (Rips.pairwiseDiscrepancy_nonneg d e))

end Rips

end TDA.Persistence
