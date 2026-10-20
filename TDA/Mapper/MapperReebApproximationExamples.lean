import TDA.Mapper.MapperReebApproximation
import TDA.Mapper.MultiNerveExamples
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Categorical Mapper approximation examples

The examples exercise actual graph realizations and interval-component maps: an edge-interior
hit missed by every vertex; a horizontal edge and a disconnected graph with repeated heights;
a loop with two intersection components over one ordinary Mapper edge; and arbitrary positive
approximation error for a nonconstant edge. A constant input with a wide member shows why a
cover member's full width cannot be replaced by its attained-range diameter.
-/

open scoped Topology ENNReal

namespace TDA.Mapper.MapperReebApproximationExamples

open Set SimpleGraph CategoryTheory Filter
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀)
open TDA.Mapper.GraphPL.Examples (overlappingIntervals)

noncomputable section

/-- A one-member cover of width two, retaining its full ambient interval. -/
def wideCover : Unit → OpenInterval := fun _ => ioo (-1) 1

private theorem flat_height {V : Type*} (G : SimpleGraph V) (x : Realization G) :
    plHeight G (fun _ => (0 : ℝ)) x = 0 := by
  have hx := plHeight_mem_Icc_of_forall (G := G) (h := fun _ => (0 : ℝ))
    (m := 0) (M := 0) (fun _ => ⟨le_rfl, le_rfl⟩) x
  exact le_antisymm hx.2 hx.1

/-- All attained heights are zero, while the assembled value over `(1/2,3/4)` is nonempty. -/
theorem constant_wide_cover_exceeds_clipped_range :
    (∀ x, plHeight edgeGraph (fun _ => (0 : ℝ)) x = 0) ∧
    IsEmpty ((intervalComponents (plHeight edgeGraph (fun _ => (0 : ℝ)))).obj
      (ioo (1 / 2) (3 / 4))) ∧
    Nonempty ((coverComponents (plHeight edgeGraph (fun _ => (0 : ℝ))) wideCover).obj
      (ioo (1 / 2) (3 / 4))) := by
  refine ⟨flat_height edgeGraph, ⟨fun c => ?_⟩, ?_⟩
  · induction c using ZerothHomotopy.rec with
    | mk x =>
      have hx := x.property
      rw [flat_height edgeGraph x.val] at hx
      change (1 / 2 : ℝ) < 0 ∧ 0 < 3 / 4 at hx
      norm_num at hx
  · exact ⟨ZerothHomotopy.mk ⟨vertex edgeGraph false,
      mem_coverSaturation.mpr ⟨(), by norm_num [wideCover, mem_ioo],
        2 / 3, by norm_num [wideCover, mem_ioo], by norm_num [mem_ioo]⟩⟩⟩

/-- Clipping the wide cover to the attained constant height gives zero resolution. -/
theorem constant_wide_cover_clipped_resolution_zero :
    clippedCoverResolution (plHeight edgeGraph (fun _ => (0 : ℝ)))
      (fun _ : Unit => -1) (fun _ => 1) = 0 := by
  have hs : ((ioo (-1) 1 : Set ℝ) ∩
      Set.range (plHeight edgeGraph (fun _ => (0 : ℝ)))).Subsingleton := by
    intro x hx y hy
    obtain ⟨u, rfl⟩ := hx.2
    obtain ⟨v, rfl⟩ := hy.2
    rw [flat_height edgeGraph u, flat_height edgeGraph v]
  unfold clippedCoverResolution
  simp only [Metric.diam_subsingleton hs, Real.toNNReal_zero]
  exact Finset.sup_bot _

/-- A wide interval on constant input has strictly positive actual reconstruction error;
clipping its width to the attained singleton would give a false zero-error bound. -/
theorem constant_wide_cover_geometric_error_pos :
    0 < RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction edgeGraph (fun _ => (0 : ℝ))
        (fun _ : Unit => -1) (fun _ => 1))
      (GraphPL.graphPLReebGraph edgeGraph (fun _ => (0 : ℝ))) := by
  apply bot_lt_iff_ne_bot.mpr
  intro hzero
  rw [geometricInterleavingDistance_mapperReeb_eq] at hzero
  obtain ⟨j⟩ := (interleavingDistance_eq_zero_iff.mp hzero) (1 / 8) (by norm_num)
  have he : IsEmpty ((intervalComponents (plHeight edgeGraph (fun _ => (0 : ℝ)))).obj
      (thicken (1 / 8) (ioo (1 / 2) (3 / 4)))) := by
    constructor
    intro c
    induction c using ZerothHomotopy.rec with
    | mk x =>
      obtain ⟨y, hy, hxy⟩ := mem_thicken.mp x.property
      rw [flat_height edgeGraph x.val] at hxy
      have hl := (abs_le.mp hxy).1
      norm_num at hl
      linarith [hy.1]
  let c := constant_wide_cover_exceeds_clipped_range.2.2.some
  exact he.false (j.φ.app (ioo (1 / 2) (3 / 4)) c)

/-- Contact at an excluded cover endpoint does not activate an open cover member. -/
theorem wide_cover_endpoint_contact_empty :
    IsEmpty ((coverComponents (plHeight edgeGraph (fun _ => (0 : ℝ))) wideCover).obj
      (ioo 1 2)) := by
  constructor
  intro c
  induction c using ZerothHomotopy.rec with
  | mk x =>
    obtain ⟨i, _, y, hyU, hyI⟩ := mem_coverSaturation.mp x.property
    change (-1 : ℝ) < y ∧ y < 1 at hyU
    exact (not_lt_of_ge hyI.1.le) hyU.2

/-- The empty graph and empty cover attain the zero-resolution geometric bound. -/
theorem empty_graph_zero_resolution :
    RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction (⊥ : SimpleGraph Empty) Empty.elim
        (fun i : Empty => i.elim) (fun i => i.elim))
      (GraphPL.graphPLReebGraph (⊥ : SimpleGraph Empty) Empty.elim) = 0 := by
  apply le_antisymm _ bot_le
  have h := geometricInterleavingDistance_mapperReeb_le (⊥ : SimpleGraph Empty) Empty.elim
    (fun i : Empty => i.elim) (fun i => i.elim) (fun x => isEmptyElim x)
  norm_num [coverResolution] at h
  exact h.le

/-- The horizontal-edge reconstruction has the geometric error bound without a strict-height
hypothesis. -/
theorem horizontal_edge_error :
    RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction edgeGraph (fun _ => (0 : ℝ))
        (fun _ : Unit => -1) (fun _ => 1))
      (GraphPL.graphPLReebGraph edgeGraph (fun _ => (0 : ℝ))) ≤ 2 := by
  have h := geometricInterleavingDistance_mapperReeb_le edgeGraph (fun _ => (0 : ℝ))
    (fun _ : Unit => -1) (fun _ => 1) (fun x => ⟨(), by
      rw [flat_height edgeGraph x]; norm_num [mem_ioo]⟩)
  norm_num [coverResolution] at h
  exact h

/-- A disconnected graph with repeated vertex heights satisfies the same actual quotient bound. -/
theorem disconnected_repeated_height_error :
    RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction (⊥ : SimpleGraph Bool) (fun _ => (0 : ℝ))
        (fun _ : Unit => -1) (fun _ => 1))
      (GraphPL.graphPLReebGraph (⊥ : SimpleGraph Bool) (fun _ => (0 : ℝ))) ≤ 2 := by
  have h := geometricInterleavingDistance_mapperReeb_le (⊥ : SimpleGraph Bool)
    (fun _ => (0 : ℝ)) (fun _ : Unit => -1) (fun _ => 1) (fun x => ⟨(), by
      rw [flat_height (⊥ : SimpleGraph Bool) x]; norm_num [mem_ioo]⟩)
  norm_num [coverResolution] at h
  exact h

/-- Retention uses the actual edge interior, even when no vertex height meets the member. -/
theorem interior_hit_retained :
    (∀ v : Bool, h02 v ∉ ioo (1 / 4) (3 / 4)) ∧
    Nonempty (RetainedCoverMember (plHeight edgeGraph h02)
      (fun _ : Unit => ioo (1 / 4) (3 / 4))) := by
  constructor
  · intro v; cases v <;> norm_num [h02, mem_ioo]
  · exact ⟨⟨(), edgePoint edgeGraph d₀ quarter, by
      change plHeight edgeGraph h02 (edgePoint edgeGraph d₀ quarter) ∈ ioo (1 / 4) (3 / 4)
      rw [plHeight_edgePoint, d₀_quarter]; norm_num [mem_ioo]⟩⟩

/-- A member wholly outside the attained range contributes no retained label. -/
theorem empty_pullback_removed :
    IsEmpty (RetainedCoverMember (plHeight edgeGraph (fun _ => (0 : ℝ)))
      (fun _ : Unit => ioo 2 100)) := by
  constructor
  rintro ⟨i, x, hx⟩
  change plHeight edgeGraph (fun _ => (0 : ℝ)) x ∈ ioo 2 100 at hx
  rw [flat_height edgeGraph x] at hx
  norm_num [mem_ioo] at hx

/-- The cover pair on the four-cycle is a genuine categorical Mapper simplex. -/
def cyclePair : CoverSimplex overlappingIntervals :=
  ⟨Finset.univ, Finset.univ_nonempty, 1, fun i _ => by
    cases i <;> norm_num [overlappingIntervals, mem_ioo]⟩

private theorem cyclePair_intersection :
    coverIntersection overlappingIntervals cyclePair = toOpens I4 := by
  ext x
  constructor
  · intro hx
    have hf := (mem_coverIntersection overlappingIntervals cyclePair x).mp hx false
      (Finset.mem_univ false)
    have ht := (mem_coverIntersection overlappingIntervals cyclePair x).mp hx true
      (Finset.mem_univ true)
    exact ⟨ht.1, hf.2⟩
  · intro hx
    apply (mem_coverIntersection overlappingIntervals cyclePair x).mpr
    intro i _
    cases i <;> change _ < x ∧ x < _ <;> constructor <;> linarith [hx.1, hx.2]

/-- Categorical Mapper retains both components over the cover intersection of the loop. -/
theorem cycle_categorical_pair_card :
    Nat.card ((categoricalMapperData (plHeight C4 h4) overlappingIntervals).obj cyclePair) = 2 := by
  change Nat.card ((componentFunctor (plHeight C4 h4)).obj
    (coverIntersection overlappingIntervals cyclePair)) = 2
  rw [cyclePair_intersection]
  exact c4_card_preimage

/-- The target cover intersection is nonempty but its pullback to two isolated vertices is
empty. Categorical Mapper retains the correct empty intersection-component set. -/
theorem disconnected_pair_pullback_empty :
    IsEmpty ((categoricalMapperData (plHeight (⊥ : SimpleGraph Bool) h02)
      overlappingIntervals).obj cyclePair) := by
  change IsEmpty ((componentFunctor (plHeight (⊥ : SimpleGraph Bool) h02)).obj
    (coverIntersection overlappingIntervals cyclePair))
  rw [cyclePair_intersection]
  have hm : ∀ p : Realization (⊥ : SimpleGraph Bool),
      plHeight (⊥ : SimpleGraph Bool) h02 p ∉ I4 :=
    TDA.Reeb.GraphRealization.ind _
      (fun v => by cases v <;> norm_num [plHeight_vertex, h02, I4, mem_ioo])
      (fun d _ => False.elim d.adj)
  constructor
  intro c
  induction c using ZerothHomotopy.rec with
  | mk x => exact hm x.val x.property

/-- Ordinary Mapper has one edge over the same pair, while categorical intersection data has
 two components; the latter are the data used by reconstruction. -/
theorem cycle_categorical_pair_distinguishes_ordinary_edge :
    Nat.card ((categoricalMapperData (plHeight C4 h4) overlappingIntervals).obj cyclePair) = 2 ∧
    MultiNerveExamples.cycleEdge.card = 2 ∧
    MultiNerveExamples.cycleEdge ∈ mapper (plHeight C4 h4)
      (fun i => (overlappingIntervals i : Set ℝ)) ∧
    (∀ s ∈ mapper (plHeight C4 h4) (fun i => (overlappingIntervals i : Set ℝ)),
      s.card = 2 → s = MultiNerveExamples.cycleEdge) :=
  by
    classical
    refine ⟨cycle_categorical_pair_card, ?_,
      MultiNerveExamples.cycle_multiNerveMapper_ne_mapper.2.2.1,
      MultiNerveExamples.cycle_multiNerveMapper_ne_mapper.2.2.2.1⟩
    unfold MultiNerveExamples.cycleEdge
    exact Finset.card_pair (fun he => Bool.false_ne_true (congrArg Sigma.fst he))

/-- A finer three-member cover separates the middle pair of strands of the four-cycle. -/
def cycleFineLeft : Fin 3 → ℝ := ![-1, 1 / 2, 5 / 4]

/-- Right endpoints of the finer four-cycle cover. -/
def cycleFineRight : Fin 3 → ℝ := ![3 / 4, 3 / 2, 3]

/-- The finer cover covers every attained height of the four-cycle. -/
theorem cycleFine_covers (x : Realization C4) :
    ∃ i, plHeight C4 h4 x ∈ ioo (cycleFineLeft i) (cycleFineRight i) := by
  have hx := plHeight_mem_Icc_of_forall (G := C4) (h := h4) (m := 0) (M := 2)
    (fun v => by fin_cases v <;> norm_num [h4]) x
  by_cases hlow : plHeight C4 h4 x < 3 / 4
  · exact ⟨0, by change (-1 : ℝ) < _ ∧ _ < 3 / 4; constructor <;> linarith [hx.1]⟩
  · by_cases hmid : plHeight C4 h4 x < 3 / 2
    · exact ⟨1, by change (1 / 2 : ℝ) < _ ∧ _ < 3 / 2; constructor <;> linarith⟩
    · exact ⟨2, by change (5 / 4 : ℝ) < _ ∧ _ < 3; constructor <;> linarith [hx.2]⟩

private theorem cycleFine_central_saturation :
    coverSaturation (fun i => ioo (cycleFineLeft i) (cycleFineRight i))
      (ioo (7 / 8) (9 / 8)) = toOpens I4 := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi, y, hyU, hyI⟩ := mem_coverSaturation.mp hx
    fin_cases i
    · change (-1 : ℝ) < y ∧ y < 3 / 4 at hyU
      change (7 / 8 : ℝ) < y ∧ y < 9 / 8 at hyI
      linarith [hyU.2, hyI.1]
    · exact hxi
    · change (5 / 4 : ℝ) < y ∧ y < 3 at hyU
      change (7 / 8 : ℝ) < y ∧ y < 9 / 8 at hyI
      linarith [hyU.1, hyI.2]
  · intro hx
    exact mem_coverSaturation.mpr ⟨1, hx, 1,
      by norm_num [cycleFineLeft, cycleFineRight, mem_ioo], by norm_num [mem_ioo]⟩

/-- The actual reconstructed graph, through its reconstruction counit, has two path components
in the middle interval; this is a property of `D P_K C_K`, beyond the categorical input data. -/
theorem cycleFine_reconstruction_central_card :
    Nat.card (((RGraph.cosheafFunctor.obj
      (graphPLMapperReconstruction C4 h4 cycleFineLeft cycleFineRight)).obj).obj
        (ioo (7 / 8) (9 / 8))) = 2 := by
  calc
    _ = Nat.card ((coverComponents (plHeight C4 h4)
        (fun i => ioo (cycleFineLeft i) (cycleFineRight i))).obj
          (ioo (7 / 8) (9 / 8))) :=
      Nat.card_congr ((categoricalMapperReconstructionIso (plHeight C4 h4)
        cycleFineLeft cycleFineRight (fun i => finite_zerothHomotopy C4 h4
          (ioo (cycleFineLeft i) (cycleFineRight i)))).app _).toEquiv
    _ = 2 := by
      change Nat.card ((componentFunctor (plHeight C4 h4)).obj
        (coverSaturation (fun i => ioo (cycleFineLeft i) (cycleFineRight i))
          (ioo (7 / 8) (9 / 8)))) = 2
      rw [cycleFine_central_saturation]
      exact c4_card_preimage

/-- The same finer reconstructed graph satisfies the actual geometric quotient error bound. -/
theorem cycleFine_geometric_error :
    RGraph.geometricInterleavingDistance
      (graphPLMapperReconstruction C4 h4 cycleFineLeft cycleFineRight)
      (GraphPL.graphPLReebGraph C4 h4) ≤ (coverResolution cycleFineLeft cycleFineRight : ℝ≥0∞) :=
  geometricInterleavingDistance_mapperReeb_le C4 h4 cycleFineLeft cycleFineRight cycleFine_covers

/-- A nonconstant edge admits actual finite categorical Mapper reconstructions at every
positive geometric error. -/
theorem nonconstant_edge_arbitrary_error {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, ∃ a b : Fin n → ℝ,
      (∀ x, ∃ i, plHeight edgeGraph h02 x ∈ ioo (a i) (b i)) ∧
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction edgeGraph h02 a b)
        (GraphPL.graphPLReebGraph edgeGraph h02) ≤ (Real.toNNReal r : ℝ≥0∞) :=
  exists_graphPLMapperReconstruction_error_le edgeGraph h02 hr

/-- Full resolutions of actual finite covers of the nonconstant edge vanish, and their
reconstructed graphs converge to its actual Reeb quotient with the corresponding error bound. -/
theorem nonconstant_edge_convergent_reconstructions :
    ∃ n : ℕ → ℕ, ∃ a b : ∀ t, Fin (n t) → ℝ,
      (∀ t x, ∃ i, plHeight edgeGraph h02 x ∈ ioo (a t i) (b t i)) ∧
      (∀ t, coverResolution (a t) (b t) ≤ Real.toNNReal (1 / ((t : ℝ) + 1))) ∧
      Tendsto (fun t => (coverResolution (a t) (b t) : ℝ≥0∞)) atTop (𝓝 0) ∧
      (∀ t, RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction edgeGraph h02 (a t) (b t))
        (GraphPL.graphPLReebGraph edgeGraph h02) ≤
          (Real.toNNReal (1 / ((t : ℝ) + 1)) : ℝ≥0∞)) ∧
      Tendsto (fun t => RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction edgeGraph h02 (a t) (b t))
        (GraphPL.graphPLReebGraph edgeGraph h02)) atTop (𝓝 0) := by
  have hex (t : ℕ) := exists_graphPLMapperCover_resolution_le edgeGraph h02
    (r := 1 / ((t : ℝ) + 1)) (by positivity)
  choose n a b hcov hres using hex
  have hinner : Tendsto (fun t : ℕ =>
      Real.toNNReal (1 / ((t : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.toNNReal_zero] using
      (continuous_real_toNNReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun t : ℕ =>
      (Real.toNNReal (1 / ((t : ℝ) + 1)) : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.coe_zero] using
      (ENNReal.continuous_coe.tendsto 0).comp hinner
  have hreslim : Tendsto (fun t => (coverResolution (a t) (b t) : ℝ≥0∞)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) (fun t => ENNReal.coe_le_coe.mpr (hres t))
  refine ⟨n, a, b, hcov, hres, hreslim, ?_, ?_⟩
  · intro t
    exact (geometricInterleavingDistance_mapperReeb_le edgeGraph h02
      (a t) (b t) (hcov t)).trans (ENNReal.coe_le_coe.mpr (hres t))
  · exact tendsto_geometricInterleavingDistance_mapperReeb edgeGraph h02
      (fun t => Fin (n t)) a b hcov hreslim

end

end TDA.Mapper.MapperReebApproximationExamples
