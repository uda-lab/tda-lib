import TDA.Topology.MeasureBifiltration
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex

/-!
# The large-face cover of a finite uniform multicover

A center belongs to the multicover precisely when it belongs to the intersection
of balls indexed by a sufficiently large Čech simplex. These intersections form
an open cover natural in mass and radius. Normalized Čech flags include into its
nerve. In a real normed ambient, all nonempty intersections are contractible.
-/

set_option autoImplicit false
universe u v
noncomputable section
namespace TDA.Topology.MeasureBifiltration
open MeasureTheory Metric
open TDA.Filtration.SubdivisionRips
variable {X : Type u} {V : Type v}
variable [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable [Fintype V] [Nonempty V]
local instance : DecidableEq V := Classical.decEq V

/-- The common open-ball intersection belonging to a labelled finite simplex. -/
def faceRegion (p : V → X) (r : ℝ) (s : Finset V) : Set X :=
  {x | ∀ v ∈ s, dist x (p v) < r}

/-- A finite uniform multicover is covered exactly by intersections indexed by
Čech simplices whose normalized cardinality reaches the positive mass threshold. -/
theorem mem_stage_uniform_iff_large_face (p : V → X) (a : Index) (x : X) :
    x ∈ stage (uniformMeasure p) a ↔ ∃ s : Finset V,
      s ∈ openCech p (radius a) ∧ mass a ≤ (s.card : ℝ) / Fintype.card V ∧
        x ∈ faceRegion p (radius a) s := by
  classical
  constructor
  · intro hx
    let s := Finset.univ.filter (fun v => p v ∈ ball x (radius a))
    have hsize : mass a ≤ (s.card : ℝ) / Fintype.card V := by
      change mass a ≤ (uniformMeasure p).real (ball x (radius a)) at hx
      simpa only [uniformMeasure_real _ measurableSet_ball, labelCount, s] using hx
    have hnonempty : s.Nonempty := by
      apply Finset.card_pos.mp
      by_contra h
      have hzero : s.card = 0 := Nat.eq_zero_of_not_pos h
      have : mass a ≤ 0 := by simpa only [hzero, Nat.cast_zero, zero_div] using hsize
      exact (mass_pos a).not_ge this
    have hregion : x ∈ faceRegion p (radius a) s := by
      intro v hv
      simpa only [Metric.mem_ball, dist_comm] using (Finset.mem_filter.mp hv).2
    exact ⟨s, ⟨hnonempty, x, hregion⟩, hsize, hregion⟩
  · rintro ⟨s, _, hsize, hregion⟩
    have hsub : s ⊆ Finset.univ.filter (fun v => p v ∈ ball x (radius a)) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [Metric.mem_ball, dist_comm] using hregion v hv⟩
    change mass a ≤ (uniformMeasure p).real (ball x (radius a))
    rw [uniformMeasure_real _ measurableSet_ball]
    apply hsize.trans
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
      (by positivity)

/-- The canonical large-face cover has precisely the actual multicover stage
as union, rather than merely an objectwise combinatorial surrogate. -/
theorem stage_uniform_eq_iUnion_large_face (p : V → X) (a : Index) :
    stage (uniformMeasure p) a =
      ⋃ (s : Finset V) (_ : s ∈ openCech p (radius a))
        (_ : mass a ≤ (s.card : ℝ) / Fintype.card V), faceRegion p (radius a) s := by
  ext x
  simpa only [Set.mem_iUnion, exists_prop] using mem_stage_uniform_iff_large_face p a x

omit [MeasurableSpace X] [OpensMeasurableSpace X] [Fintype V] [Nonempty V] in
/-- Every intersection in the cover is open. -/
theorem isOpen_faceRegion (p : V → X) (r : ℝ) (s : Finset V) :
    IsOpen (faceRegion p r s) := by
  classical
  have : faceRegion p r s = ⋂ v ∈ s, ball (p v) r := by ext x; simp [faceRegion]
  rw [this]
  exact isOpen_biInter_finset (fun _ _ => isOpen_ball)

/-- Invalid indices contribute the empty member, keeping a fixed vertex type
as mass decreases and radius increases. -/
noncomputable def largeFaceCover (p : V → X) (a : Index) (s : Finset V) : Set X := by
  classical
  exact if s ∈ openCech p (radius a) ∧ mass a ≤ (s.card : ℝ) / Fintype.card V then
    faceRegion p (radius a) s else ∅

omit [MeasurableSpace X] [OpensMeasurableSpace X] [Nonempty V] in
/-- The large-face cover is monotone in both filtration coordinates. -/
theorem largeFaceCover_mono (p : V → X) {a b : Index} (hab : a ≤ b) (s : Finset V) :
    largeFaceCover p a s ⊆ largeFaceCover p b s := by
  classical
  intro x hx
  unfold largeFaceCover at hx ⊢
  split_ifs at hx with ha
  · have hregion : x ∈ faceRegion p (radius b) s :=
      fun v hv => (hx v hv).trans_le hab.2
    have hcech : s ∈ openCech p (radius b) := ⟨ha.1.1, x, hregion⟩
    rw [if_pos ⟨hcech, hab.1.trans ha.2⟩]
    exact hregion
  · exact hx.elim

omit [MeasurableSpace X] [OpensMeasurableSpace X] [Nonempty V] in
/-- Every normalized Čech flag is a face of the nerve of the actual large-face
cover. A maximal member supplies a common center for the entire flag. -/
theorem subdivision_openCech_le_largeFaceNerve (p : V → X) (a : Index) :
    subdivision (openCech p (radius a)) (mass a) ≤ TDA.Topology.nerve (largeFaceCover p a) := by
  classical
  intro S hS
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image S Finset.card hS.1
  obtain ⟨x, hx⟩ := (hS.2.1 s hs).1.2
  refine ⟨hS.1, x, ?_⟩
  intro t ht
  have hts : t ⊆ s := by
    rcases hS.2.2 t ht s hs with hts | hst
    · exact hts
    · have heq := Finset.eq_of_subset_of_card_le hst (hmax t ht)
      exact heq ▸ Finset.Subset.refl s
  unfold largeFaceCover
  rw [if_pos (hS.2.1 t ht)]
  exact fun v hv => hx v (hts hv)

/-- The cover has the actual multicover stage as union on its fixed index type. -/
theorem stage_uniform_eq_iUnion_largeFaceCover (p : V → X) (a : Index) :
    stage (uniformMeasure p) a = ⋃ s : Finset V, largeFaceCover p a s := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hsize, hregion⟩ := (mem_stage_uniform_iff_large_face p a x).mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨s, ?_⟩
    unfold largeFaceCover
    rw [if_pos ⟨hs, hsize⟩]
    exact hregion
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    unfold largeFaceCover at hs
    split_ifs at hs with h
    · exact (mem_stage_uniform_iff_large_face p a x).mpr ⟨s, h.1, h.2, hs⟩
    · exact hs.elim

omit [MeasurableSpace X] [OpensMeasurableSpace X] [Nonempty V] in
/-- An intersection of large-face cover members is nonempty precisely when
the union of their labels is a Čech simplex. -/
theorem mem_largeFaceNerve_iff (p : V → X) (a : Index) (S : Finset (Finset V)) :
    S ∈ TDA.Topology.nerve (largeFaceCover p a) ↔
      S.Nonempty ∧ (∀ s ∈ S, s ∈ openCech p (radius a) ∧
        mass a ≤ (s.card : ℝ) / Fintype.card V) ∧
      S.biUnion id ∈ openCech p (radius a) := by
  classical
  constructor
  · rintro ⟨hS, x, hx⟩
    have hvalid : ∀ s ∈ S, s ∈ openCech p (radius a) ∧
        mass a ≤ (s.card : ℝ) / Fintype.card V := by
      intro s hs
      by_contra h
      have := hx s hs
      simp only [largeFaceCover, if_neg h, Set.mem_empty_iff_false] at this
    have hregion : ∀ s ∈ S, x ∈ faceRegion p (radius a) s := by
      intro s hs
      simpa only [largeFaceCover, if_pos (hvalid s hs)] using hx s hs
    refine ⟨hS, hvalid, ?_⟩
    obtain ⟨s, hs⟩ := hS
    obtain ⟨v, hv⟩ := (hvalid s hs).1.1
    refine ⟨⟨v, Finset.mem_biUnion.mpr ⟨s, hs, hv⟩⟩, x, ?_⟩
    intro v hv
    obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hv
    exact hregion t ht v hvt
  · rintro ⟨hS, hvalid, _, x, hx⟩
    refine ⟨hS, x, ?_⟩
    intro s hs
    unfold largeFaceCover
    rw [if_pos (hvalid s hs)]
    exact fun v hv => hx v (Finset.mem_biUnion.mpr ⟨s, hs, hv⟩)

/-- The nerves of the large-face cover form an actual bifiltration on the same
fixed finite-subset vertices as the normalized subdivision. -/
def largeFaceNerveBifiltration (p : V → X) :
    TDA.Filtration.SimplicialFiltration Index (Finset V) where
  toFun a := TDA.Topology.nerve (largeFaceCover p a)
  monotone' := fun _ _ hab => TDA.Topology.nerve_mono (largeFaceCover_mono p hab)

omit [MeasurableSpace X] [OpensMeasurableSpace X] [Nonempty V] in
/-- Every member of the fixed large-face cover is open, including its invalid
indices, which contribute the empty set. -/
theorem isOpen_largeFaceCover (p : V → X) (a : Index) (s : Finset V) :
    IsOpen (largeFaceCover p a s) := by
  classical
  unfold largeFaceCover
  split_ifs
  · exact isOpen_faceRegion p (radius a) s
  · exact isOpen_empty

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype V] [Nonempty V] in
/-- Common ball intersections are convex in the finite sup-norm ambient used
for the Čech/Rips identification, and in every real normed ambient space. -/
theorem convex_faceRegion (p : V → E) (r : ℝ) (s : Finset V) :
    Convex ℝ (faceRegion p r s) := by
  have heq : faceRegion p r s = ⋂ v ∈ s, ball (p v) r := by ext x; simp [faceRegion]
  rw [heq]
  exact convex_iInter₂ (fun _ _ => convex_ball _ _)

omit [Nonempty V] in
/-- Empty invalid members and valid ball intersections are both convex. -/
theorem convex_largeFaceCover (p : V → E) (a : Index) (s : Finset V) :
    Convex ℝ (largeFaceCover p a s) := by
  classical
  unfold largeFaceCover
  split_ifs
  · exact convex_faceRegion p (radius a) s
  · exact convex_empty

omit [Nonempty V] in
/-- Every nonempty finite intersection in the actual multicover cover is
contractible, discharging the good-cover hypothesis in a real normed ambient. -/
theorem contractibleSpace_largeFaceCover_intersection (p : V → E) (a : Index)
    (S : Finset (Finset V))
    (h : (⋂ s ∈ S, largeFaceCover p a s).Nonempty) :
    ContractibleSpace (⋂ s ∈ S, largeFaceCover p a s) :=
  (convex_iInter₂ (fun s _ => convex_largeFaceCover p a s)).contractibleSpace h

end TDA.Topology.MeasureBifiltration


end
