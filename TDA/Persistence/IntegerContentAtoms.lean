import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
# Positive atoms of integer contents

An additive content with natural-number values on open cells has a positive point atom
inside every compact cell of positive content. The multiplicity at a point is the minimum
of the values of its containing cells. If every multiplicity vanished, zero-content open
cells would cover the compact cell. A finite subcover and finite-cover subadditivity would
then force its content to vanish. Subtracting a point content and inducting on the
compact cell value gives a finite local atomic representation. For a separating cell
family, the minimum cell values recover the point counts and have locally finite support.

These are atomicity results for mathlib's actual additive contents. The companion module
`PersistenceMeasureContent` constructs the additive content of a q-tame persistence module.
-/

universe v

namespace TDA.Persistence.RectangleMeasure

open Set MeasureTheory
open scoped Classical

variable {X : Type v} {C : Set (Set X)}

/-- Minimum content of the cells containing a point. Containment in one cell guarantees
that this minimum is attained. -/
noncomputable def contentMultiplicity (m : AddContent ℕ C) (x : X) : ℕ :=
  sInf {n | ∃ U ∈ C, x ∈ U ∧ m U = n}

/-- Point multiplicity is bounded by every containing cell's content. -/
theorem contentMultiplicity_le (m : AddContent ℕ C) {x : X} {U : Set X}
    (hU : U ∈ C) (hx : x ∈ U) : contentMultiplicity m x ≤ m U :=
  csInf_le' ⟨U, hU, hx, rfl⟩

/-- A point seen by the cells has a cell attaining its multiplicity. -/
theorem exists_cell_eq_contentMultiplicity (m : AddContent ℕ C) (x : X)
    (hx : ∃ U ∈ C, x ∈ U) :
    ∃ U ∈ C, x ∈ U ∧ m U = contentMultiplicity m x := by
  exact csInf_mem (s := {n | ∃ U ∈ C, x ∈ U ∧ m U = n}) (by
    obtain ⟨U, hU, hxU⟩ := hx
    exact ⟨m U, U, hU, hxU, rfl⟩)

/-- Compactness and integer-valued finite additivity produce an actual positive point atom. -/
theorem exists_positive_content_atom [TopologicalSpace X] (hC : IsSetSemiring C)
    (m : AddContent ℕ C) (hOpen : ∀ U ∈ C, IsOpen U) {K : Set X}
    (hK : K ∈ C) (hCompact : IsCompact K) (hpos : 0 < m K) :
    ∃ x ∈ K, 0 < contentMultiplicity m x := by
  classical
  by_contra hn
  let Z := {U : Set X // U ∈ C ∧ m U = 0}
  have hcover : K ⊆ ⋃ U : Z, U.val := by
    intro x hx
    have hz : contentMultiplicity m x = 0 := by
      by_contra hne
      exact hn ⟨x, hx, Nat.pos_of_ne_zero hne⟩
    obtain ⟨U, hUC, hxU, heq⟩ := exists_cell_eq_contentMultiplicity m x ⟨K, hK, hx⟩
    exact mem_iUnion.mpr ⟨⟨U, hUC, heq.trans hz⟩, hxU⟩
  obtain ⟨t, ht⟩ := hCompact.elim_finite_subcover (fun U : Z => U.val)
    (fun U => hOpen U.val U.property.1) hcover
  let J : Finset (Set X) := t.image Subtype.val
  have hJC : (J : Set (Set X)) ⊆ C := by
    intro U hU
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hU
    exact V.property.1
  have hKJ : K ⊆ ⋃₀ (J : Set (Set X)) := by
    intro x hx
    obtain ⟨U, hUt, hxU⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_sUnion.mpr ⟨U.val, Finset.mem_image.mpr ⟨U, hUt, rfl⟩, hxU⟩
  have hle := addContent_le_sum_of_subset_sUnion (m := m) hC hJC hK hKJ
  have hsum : ∑ U ∈ J, m U = 0 := by
    apply Finset.sum_eq_zero
    intro U hU
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hU
    exact V.property.2
  rw [hsum] at hle
  exact (not_lt_of_ge hle) hpos

/-- The natural-valued content carried by one point. -/
noncomputable def pointContent (x : X) : AddContent ℕ C := by
  classical
  refine ⟨fun U => if x ∈ U then 1 else 0, by simp, ?_⟩
  intro I _ hdis _
  by_cases hx : x ∈ ⋃₀ (I : Set (Set X))
  · obtain ⟨U, hUI, hxU⟩ := mem_sUnion.mp hx
    rw [if_pos hx]
    symm
    rw [Finset.sum_eq_single U]
    · simp only [if_pos hxU]
    · intro V hVI hVU
      have hxV : x ∉ V := by
        intro hxV
        exact Set.disjoint_left.mp (hdis hVI hUI hVU) hxV hxU
      simp [hxV]
    · exact fun hn => (hn hUI).elim
  · rw [if_neg hx]
    symm
    apply Finset.sum_eq_zero
    intro U hUI
    have hxU : x ∉ U := fun hxU => hx (mem_sUnion.mpr ⟨U, hUI, hxU⟩)
    simp [hxU]

/-- A positive point multiplicity permits subtracting one copy of its point content. -/
theorem pointContent_le (m : AddContent ℕ C) {x : X}
    (hx : 0 < contentMultiplicity m x) {U : Set X} (hU : U ∈ C) :
    pointContent (C := C) x U ≤ m U := by
  classical
  change (if x ∈ U then 1 else 0) ≤ m U
  split_ifs with hxU
  · exact (Nat.succ_le_iff.mpr hx).trans (contentMultiplicity_le m hU hxU)
  · exact Nat.zero_le _

/-- Remove one copy of a positive atom, retaining a natural-valued additive content. -/
noncomputable def subtractPointContent (m : AddContent ℕ C) (x : X)
    (hx : 0 < contentMultiplicity m x) : AddContent ℕ C where
  toFun U := m U - pointContent (C := C) x U
  empty' := by simp
  sUnion' I hIC hdis hUnion := by
    have hleft := Nat.sub_add_cancel (pointContent_le m hx hUnion)
    have hright : ∑ U ∈ I, (m U - pointContent (C := C) x U) +
        ∑ U ∈ I, pointContent (C := C) x U = ∑ U ∈ I, m U := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun U hU => Nat.sub_add_cancel (pointContent_le m hx (hIC hU))
    apply Nat.add_right_cancel (m := ∑ U ∈ I, pointContent (C := C) x U)
    rw [← addContent_sUnion (m := pointContent (C := C) x) hIC hdis hUnion, hleft]
    rw [addContent_sUnion (m := pointContent (C := C) x) hIC hdis hUnion, hright]
    exact addContent_sUnion hIC hdis hUnion

/-- Removing a point subtracts its incidence from every set's value. -/
theorem subtractPointContent_apply (m : AddContent ℕ C) (x : X)
    (hx : 0 < contentMultiplicity m x) (U : Set X) :
    subtractPointContent m x hx U = m U - if x ∈ U then 1 else 0 := rfl

/-- Every compact cell has a finite atomic representation of all its subcell counts.
The multiset is local to this compact cell; no global finiteness is asserted. -/
theorem exists_local_atomic_representation [TopologicalSpace X] (hC : IsSetSemiring C)
    (m : AddContent ℕ C) (hOpen : ∀ U ∈ C, IsOpen U) {K : Set X}
    (hK : K ∈ C) (hCompact : IsCompact K) :
    ∃ points : Multiset X, (∀ x ∈ points, x ∈ K) ∧
      ∀ U ∈ C, U ⊆ K → m U = (points.filter (· ∈ U)).card := by
  have haux : ∀ n (m : AddContent ℕ C), m K = n →
      ∃ points : Multiset X, (∀ x ∈ points, x ∈ K) ∧
        ∀ U ∈ C, U ⊆ K → m U = (points.filter (· ∈ U)).card := by
    intro n
    induction n with
    | zero =>
      intro m hm
      refine ⟨0, by simp, ?_⟩
      intro U hU hUK
      have hle := addContent_mono (m := m) hC hU hK hUK
      simp only [Multiset.filter_zero, Multiset.card_zero]
      omega
    | succ n ih =>
      intro m hm
      obtain ⟨x, hxK, hx⟩ := exists_positive_content_atom hC m hOpen hK hCompact (by omega)
      let m' := subtractPointContent m x hx
      have hm' : m' K = n := by
        change m K - (if x ∈ K then 1 else 0) = n
        rw [if_pos hxK, hm]
        omega
      obtain ⟨points, hpoints, hrepr⟩ := ih m' hm'
      refine ⟨x ::ₘ points, ?_, ?_⟩
      · intro y hy
        rcases Multiset.mem_cons.mp hy with rfl | hy
        · exact hxK
        · exact hpoints y hy
      · intro U hU hUK
        have hcount := hrepr U hU hUK
        have hrestore := Nat.sub_add_cancel (pointContent_le m hx hU)
        change (m U - (if x ∈ U then 1 else 0)) + (if x ∈ U then 1 else 0) = m U at hrestore
        change m U - (if x ∈ U then 1 else 0) = _ at hcount
        by_cases hxU : x ∈ U
        · simp only [hxU, if_true] at hcount hrestore
          simp only [Multiset.filter_cons_of_pos _ hxU, Multiset.card_cons]
          rw [← hcount]
          exact hrestore.symm
        · simp only [hxU, if_false, Nat.sub_zero] at hcount
          simpa only [Multiset.filter_cons_of_neg _ hxU] using hcount
  exact haux (m K) m rfl

/-- Finitely many points can be separated from a point inside a prescribed cell. -/
theorem exists_cell_separating_multiset (hC : IsSetSemiring C) {x : X}
    (hSep : ∀ y : X, x ≠ y → ∃ U ∈ C, x ∈ U ∧ y ∉ U)
    (points : Multiset X) {K : Set X} (hK : K ∈ C) (hxK : x ∈ K) :
    ∃ U ∈ C, x ∈ U ∧ U ⊆ K ∧ ∀ y ∈ points, y ∈ U → y = x := by
  induction points using Multiset.induction_on with
  | empty => exact ⟨K, hK, hxK, subset_rfl, by simp⟩
  | @cons y points ih =>
    obtain ⟨U, hU, hxU, hUK, hpoints⟩ := ih
    by_cases hyx : y = x
    · refine ⟨U, hU, hxU, hUK, ?_⟩
      intro z hz hzU
      rcases Multiset.mem_cons.mp hz with rfl | hz
      · exact hyx
      · exact hpoints z hz hzU
    · obtain ⟨V, hV, hxV, hyV⟩ := hSep y (Ne.symm hyx)
      refine ⟨U ∩ V, hC.inter_mem _ hU _ hV, ⟨hxU, hxV⟩,
        inter_subset_left.trans hUK, ?_⟩
      intro z hz hzUV
      rcases Multiset.mem_cons.mp hz with rfl | hz
      · exact (hyV hzUV.2).elim
      · exact hpoints z hz hzUV.1

/-- On a cell with a finite atomic representation, minimum cell content recovers each
point's actual multiplicity. Separation of points is the uniqueness hypothesis. -/
theorem contentMultiplicity_eq_count (hC : IsSetSemiring C) {x : X}
    (hSep : ∀ y : X, x ≠ y → ∃ U ∈ C, x ∈ U ∧ y ∉ U)
    (m : AddContent ℕ C) {K : Set X} (hK : K ∈ C) (points : Multiset X)
    (hRepr : ∀ U ∈ C, U ⊆ K → m U = (points.filter (· ∈ U)).card)
    (hxK : x ∈ K) : contentMultiplicity m x = points.count x := by
  classical
  apply le_antisymm
  · obtain ⟨U, hU, hxU, hUK, hOnly⟩ :=
      exists_cell_separating_multiset hC hSep points hK hxK
    have hfilter : points.filter (· ∈ U) = points.filter (· = x) := by
      apply Multiset.filter_congr
      intro y hy
      constructor
      · exact hOnly y hy
      · rintro rfl
        exact hxU
    calc contentMultiplicity m x ≤ m U := contentMultiplicity_le m hU hxU
      _ = (points.filter (· ∈ U)).card := hRepr U hU hUK
      _ = points.count x := by
        rw [hfilter]
        simpa using congrArg Multiset.card (Multiset.filter_eq' points x)
  · obtain ⟨V, hV, hxV, hmin⟩ := exists_cell_eq_contentMultiplicity m x ⟨K, hK, hxK⟩
    have hKV := hC.inter_mem K hK V hV
    calc points.count x = (points.filter (· ∈ K ∩ V)).count x :=
        (Multiset.count_filter_of_pos ⟨hxK, hxV⟩).symm
      _ ≤ (points.filter (· ∈ K ∩ V)).card := Multiset.count_le_card _ _
      _ = m (K ∩ V) := by
        convert (hRepr _ hKV inter_subset_left).symm using 2
        congr 1
      _ ≤ m V := addContent_mono hC hKV hV inter_subset_right
      _ = contentMultiplicity m x := hmin

/-- Positive multiplicity has finite support on every compact cell of a separating open
semiring. This is local finiteness, without asserting finite global support. -/
theorem finite_positive_content_support [TopologicalSpace X] (hC : IsSetSemiring C)
    (m : AddContent ℕ C) (hOpen : ∀ U ∈ C, IsOpen U)
    {K : Set X} (hSep : ∀ x ∈ K, ∀ y : X, x ≠ y → ∃ U ∈ C, x ∈ U ∧ y ∉ U)
    (hK : K ∈ C) (hCompact : IsCompact K) :
    Set.Finite {x | x ∈ K ∧ 0 < contentMultiplicity m x} := by
  classical
  obtain ⟨points, _, hRepr⟩ := exists_local_atomic_representation hC m hOpen hK hCompact
  apply points.toFinset.finite_toSet.subset
  intro x hx
  change x ∈ K ∧ 0 < contentMultiplicity m x at hx
  rw [contentMultiplicity_eq_count hC (hSep x hx.1) m hK points hRepr hx.1] at hx
  exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hx.2)

/-- The minimum-cell multiplicity reconstructs the mass of every compact cell exactly. -/
theorem content_eq_sum_multiplicity [TopologicalSpace X] (hC : IsSetSemiring C)
    (m : AddContent ℕ C) (hOpen : ∀ U ∈ C, IsOpen U)
    {K : Set X} (hSep : ∀ x ∈ K, ∀ y : X, x ≠ y → ∃ U ∈ C, x ∈ U ∧ y ∉ U)
    (hK : K ∈ C) (hCompact : IsCompact K) :
    ∃ S : Finset X, (∀ x, x ∈ S ↔ x ∈ K ∧ 0 < contentMultiplicity m x) ∧
      m K = ∑ x ∈ S, contentMultiplicity m x := by
  classical
  obtain ⟨points, hpoints, hRepr⟩ := exists_local_atomic_representation hC m hOpen hK hCompact
  have hcount := fun x hxK => contentMultiplicity_eq_count hC (hSep x hxK) m hK points hRepr hxK
  refine ⟨points.toFinset, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hxpoints := Multiset.mem_toFinset.mp hx
      have hxK := hpoints x hxpoints
      exact ⟨hxK, (hcount x hxK).symm ▸ Multiset.count_pos.mpr hxpoints⟩
    · rintro ⟨hxK, hxpos⟩
      rw [hcount x hxK] at hxpos
      exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hxpos)
  · calc m K = points.card := by
          rw [hRepr K hK subset_rfl, Multiset.filter_eq_self.mpr hpoints]
         _ = ∑ x ∈ points.toFinset, points.count x := points.toFinset_sum_count_eq.symm
         _ = ∑ x ∈ points.toFinset, contentMultiplicity m x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (hcount x (hpoints x (Multiset.mem_toFinset.mp hx))).symm

end TDA.Persistence.RectangleMeasure
