import TDA.Filtration.FilterFunction
import Mathlib.Topology.MetricSpace.Basic

/-!
# Diameter filtrations on a fixed labelled vertex set

Metric structures are explicit arguments, so two metrics on the same carrier do
not compete as global instances. The full complex has all nonempty finite faces.
Its face value is diameter, with singleton value zero; the auxiliary diameter of
the empty set is zero, but the empty set is never a face. Sublevels use the closed
distance threshold itself, with no conversion to a ball radius.
-/

universe u

namespace TDA.Filtration.Rips

open TDA.Simplicial

variable {V : Type u}

/-- The full simplex complex, containing precisely the nonempty finite subsets. -/
def fullComplex (V : Type u) : PreAbstractSimplicialComplex V := ⊤

@[simp] theorem mem_fullComplex_iff (s : Finset V) :
    s ∈ fullComplex V ↔ s.Nonempty := Iff.rfl

/-- Finitely many vertices give finitely many actual faces, without assuming a vertex exists. -/
noncomputable instance fullComplexFintype [Fintype V] : Fintype (TotalFace (fullComplex V)) :=
  Fintype.ofFinite _

/-- The maximum pairwise distance, with empty maximum zero. -/
noncomputable def diameter (d : MetricSpace V) (s : Finset V) : ℝ :=
  (s ×ˢ s).fold max 0 (fun p => d.dist p.1 p.2)

private theorem distance_nonneg (d : MetricSpace V) (v w : V) : 0 ≤ d.dist v w := by
  let : MetricSpace V := d
  exact dist_nonneg

@[simp] theorem diameter_empty (d : MetricSpace V) : diameter d ∅ = 0 := by
  classical
  simp [diameter]

@[simp] theorem diameter_singleton (d : MetricSpace V) (v : V) : diameter d {v} = 0 := by
  classical
  simp [diameter]

theorem diameter_nonneg (d : MetricSpace V) (s : Finset V) : 0 ≤ diameter d s := by
  classical
  exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

/-- The zero seed records the auxiliary empty-set convention explicitly. -/
theorem diameter_le_iff (d : MetricSpace V) (s : Finset V) (r : ℝ) :
    diameter d s ≤ r ↔ 0 ≤ r ∧ ∀ v ∈ s, ∀ w ∈ s, d.dist v w ≤ r := by
  classical
  unfold diameter
  rw [Finset.fold_max_le]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, fun v hv w hw => h (v, w) (Finset.mem_product.mpr ⟨hv, hw⟩)⟩
  · rintro ⟨hr, h⟩
    exact ⟨hr, fun p hp => h p.1 (Finset.mem_product.mp hp).1 p.2
      (Finset.mem_product.mp hp).2⟩

theorem dist_le_diameter (d : MetricSpace V) {s : Finset V} {v w : V}
    (hv : v ∈ s) (hw : w ∈ s) : d.dist v w ≤ diameter d s := by
  classical
  exact (Finset.le_fold_max _).mpr
    (Or.inr ⟨(v, w), Finset.mem_product.mpr ⟨hv, hw⟩, le_rfl⟩)

/-- A face with at least two vertices has positive diameter. -/
theorem diameter_pos (d : MetricSpace V) {s : Finset V} (hs : 1 < s.card) :
    0 < diameter d s := by
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.1 hs
  let : MetricSpace V := d
  exact (dist_pos.2 hvw).trans_le (dist_le_diameter d hv hw)

theorem diameter_mono (d : MetricSpace V) {s t : Finset V} (hst : s ⊆ t) :
    diameter d s ≤ diameter d t := by
  apply (diameter_le_iff d s _).mpr
  exact ⟨diameter_nonneg d t, fun _ hv _ hw => dist_le_diameter d (hst hv) (hst hw)⟩

/-- In particular, the entry time of an edge is its distance, not half its distance. -/
theorem diameter_pair [DecidableEq V] (d : MetricSpace V) (v w : V) :
    diameter d {v, w} = d.dist v w := by
  classical
  apply le_antisymm
  · apply (diameter_le_iff d _ _).mpr
    refine ⟨distance_nonneg d v w, ?_⟩
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [d.dist_comm]
  · exact dist_le_diameter d (by simp) (by simp)

/-- The real-valued diameter filter on all actual faces. -/
noncomputable def filter (d : MetricSpace V) : FilterFunction (fullComplex V) ℝ where
  value s := diameter d s.val
  mono h := diameter_mono d h

@[simp] theorem filter_value (d : MetricSpace V) (s : TotalFace (fullComplex V)) :
    (filter d).value s = diameter d s.val := rfl

/-- The closed Rips condition includes self-pairs, so a singleton first appears at zero. -/
theorem mem_sublevel_iff (d : MetricSpace V) (r : ℝ) (s : Finset V) :
    s ∈ (filter d).sublevel r ↔ s.Nonempty ∧ ∀ v ∈ s, ∀ w ∈ s, d.dist v w ≤ r := by
  rw [FilterFunction.mem_sublevel_iff]
  constructor
  · rintro ⟨hs, hr⟩
    exact ⟨hs, ((diameter_le_iff d s r).mp hr).2⟩
  · rintro ⟨hs, h⟩
    refine ⟨hs, (diameter_le_iff d s r).mpr ⟨?_, h⟩⟩
    obtain ⟨v, hv⟩ := hs
    simpa only [d.dist_self] using h v hv v hv

theorem sublevel_eq_bot_of_neg (d : MetricSpace V) {r : ℝ} (hr : r < 0) :
    (filter d).sublevel r = ⊥ :=
  (filter d).sublevel_eq_bot_of_forall_lt r
    (fun s => hr.trans_le (diameter_nonneg d s.val))

section FiniteVertices

variable [Fintype V]

/-- Maximum discrepancy between the two distance matrices; zero on an empty carrier. -/
noncomputable def pairwiseDiscrepancy (d e : MetricSpace V) : ℝ :=
  Finset.univ.fold max 0 (fun p : V × V => |d.dist p.1 p.2 - e.dist p.1 p.2|)

theorem pairwiseDiscrepancy_nonneg (d e : MetricSpace V) :
    0 ≤ pairwiseDiscrepancy d e := by
  classical
  exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

theorem abs_dist_sub_le_pairwiseDiscrepancy (d e : MetricSpace V) (v w : V) :
    |d.dist v w - e.dist v w| ≤ pairwiseDiscrepancy d e := by
  classical
  exact (Finset.le_fold_max _).mpr
    (Or.inr ⟨(v, w), Finset.mem_univ _, le_rfl⟩)

@[simp] theorem pairwiseDiscrepancy_self (d : MetricSpace V) :
    pairwiseDiscrepancy d d = 0 := by
  classical
  apply le_antisymm _ (pairwiseDiscrepancy_nonneg d d)
  exact (Finset.fold_max_le 0).mpr ⟨le_rfl, fun _ _ => by simp⟩

@[simp] theorem pairwiseDiscrepancy_of_isEmpty [IsEmpty V] (d e : MetricSpace V) :
    pairwiseDiscrepancy d e = 0 := by
  classical
  simp [pairwiseDiscrepancy]

/-- Taking diameters cannot enlarge the maximum pairwise discrepancy. -/
theorem abs_diameter_sub_le_pairwiseDiscrepancy (d e : MetricSpace V) (s : Finset V) :
    |diameter d s - diameter e s| ≤ pairwiseDiscrepancy d e := by
  have hδ := pairwiseDiscrepancy_nonneg d e
  have hpair := abs_dist_sub_le_pairwiseDiscrepancy d e
  have hde : diameter d s ≤ diameter e s + pairwiseDiscrepancy d e := by
    apply (diameter_le_iff d s _).mpr
    refine ⟨add_nonneg (diameter_nonneg e s) hδ, ?_⟩
    intro v hv w hw
    have h := (abs_sub_le_iff.mp (hpair v w)).1
    have he := dist_le_diameter e hv hw
    linarith
  have hed : diameter e s ≤ diameter d s + pairwiseDiscrepancy d e := by
    apply (diameter_le_iff e s _).mpr
    refine ⟨add_nonneg (diameter_nonneg d s) hδ, ?_⟩
    intro v hv w hw
    have h := (abs_sub_le_iff.mp (hpair v w)).2
    have hd := dist_le_diameter d hv hw
    linarith
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end FiniteVertices
end TDA.Filtration.Rips
