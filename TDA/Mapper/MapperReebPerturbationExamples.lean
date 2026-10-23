import TDA.Mapper.MapperReebPerturbation
import TDA.Mapper.MapperReebApproximationExamples
import TDA.Mapper.GraphPLReebStabilityExamples

/-!
# Two-input Mapper reconstruction: fixtures

M1. With one cover and equal heights the reconstructions coincide, so the distance is `0`, while
the same-cover bound is the positive number `2 res`: the bound is not an equality.

M2. On the single edge with heights `(0, 2)` and its vertical translate `(1, 3)`, covers with
vanishing resolution give reconstructions whose distance tends to `1`, the exact Reeb distance of
the translation.

M3. On the four-cycle, raising the apex height `2` by `1/8` gives distance at most
`2 res + 1/8` and at least `1/8 - 2 res`.

M4. On two disjoint edges, with arbitrary covers, the maximal-height lower bound is `1`;
connectedness is not used.

M5. The empty cover of a nonempty graph reconstructs the empty graph, which is at distance `⊤`
from the Reeb quotient; the coverage hypothesis cannot be dropped.

M6. On an empty vertex type every distance is `0`.

M7. The cosheaf-level bound, together with the identification of the reconstruction distance
with the assembled interleaving distance, reproduces the geometric upper bound.
-/

open scoped NNReal ENNReal Topology

namespace TDA.Mapper.MapperReebPerturbationExamples

open Set SimpleGraph Filter CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Mapper.GraphPL
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph twoEdges fst_eq_of_reachable)
open TDA.Mapper.MapperReebApproximationExamples
  (cycleFineLeft cycleFineRight cycleFine_covers nonconstant_edge_convergent_reconstructions)
open TDA.Mapper.GraphPLReebStabilityExamples (twoEdgesHeight twoEdgesRaised)

noncomputable section

/-! ## M1. Equal heights -/

theorem cycleFine_coverResolution_pos : 0 < coverResolution cycleFineLeft cycleFineRight := by
  have := width_le_coverResolution cycleFineLeft cycleFineRight 0
  have h0 : cycleFineRight 0 - cycleFineLeft 0 = 7 / 4 := by
    norm_num [cycleFineLeft, cycleFineRight]
  have h : (0 : ℝ) < coverResolution cycleFineLeft cycleFineRight := by linarith
  exact_mod_cast h

/-- With equal heights and one cover the distance is `0` and the same-cover bound is positive. -/
theorem equal_heights_same_cover :
    RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction C4 h4 cycleFineLeft cycleFineRight)
        (graphPLMapperReconstruction C4 h4 cycleFineLeft cycleFineRight) = 0 ∧
      RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction C4 h4 cycleFineLeft cycleFineRight)
        (graphPLMapperReconstruction C4 h4 cycleFineLeft cycleFineRight) ≤
        2 * (coverResolution cycleFineLeft cycleFineRight : ℝ≥0∞) + edist h4 h4 ∧
      0 < 2 * (coverResolution cycleFineLeft cycleFineRight : ℝ≥0∞) + edist h4 h4 := by
  refine ⟨RGraph.geometricInterleavingDistance_self _,
    geometricInterleavingDistance_mapperReeb_le_two_mul_add_edist C4 h4 h4 _ _
      cycleFine_covers cycleFine_covers, ?_⟩
  rw [show edist h4 h4 = 0 by simp, add_zero]
  exact ENNReal.mul_pos two_ne_zero (by exact_mod_cast cycleFine_coverResolution_pos.ne')

/-! ## M2. Translation limit -/

/-- The piecewise-linear height of a vertical translate is the translate of the height. -/
theorem plHeight_add_const {V : Type} (G : SimpleGraph V) (h : V → ℝ) (c : ℝ)
    (x : Realization G) : plHeight G (fun v => h v + c) x = plHeight G h x + c := by
  have := plHeight_unique G (fun v => h v + c)
    (plHeight G h + ContinuousMap.const (Realization G) c)
    (fun v => by simp) (fun d t => by
      simp only [ContinuousMap.add_apply, plHeight_edgePoint, ContinuousMap.const_apply,
        dartHeight]
      ring)
  rw [← this]
  rfl

/-- Translating a cover by `c` preserves its resolution. -/
theorem coverResolution_add_const {ι : Type} [Finite ι] (a b : ι → ℝ) (c : ℝ) :
    coverResolution (fun i => a i + c) (fun i => b i + c) = coverResolution a b := by
  unfold coverResolution
  simp

/-- Covers of the edge with heights `(0, 2)` and the translated covers of its translate by `1`
have vanishing resolutions, and the distance of the reconstructions tends to `1`. -/
theorem translation_limit :
    ∃ n : ℕ → ℕ, ∃ a b : ∀ t, Fin (n t) → ℝ,
      (∀ t x, ∃ i, plHeight edgeGraph h02 x ∈ ioo (a t i) (b t i)) ∧
      (∀ t x, ∃ i, plHeight edgeGraph (fun v => h02 v + 1) x ∈
        ioo (a t i + 1) (b t i + 1)) ∧
      Tendsto (fun t => RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction edgeGraph h02 (a t) (b t))
        (graphPLMapperReconstruction edgeGraph (fun v => h02 v + 1)
          (fun i => a t i + 1) (fun i => b t i + 1))) atTop (𝓝 1) := by
  obtain ⟨n, a, b, hcov, -, hres, -, -⟩ := nonconstant_edge_convergent_reconstructions
  have hcov' : ∀ t x, ∃ i, plHeight edgeGraph (fun v => h02 v + 1) x ∈
      ioo (a t i + 1) (b t i + 1) := by
    intro t x
    obtain ⟨i, hi⟩ := hcov t x
    refine ⟨i, ?_⟩
    rw [plHeight_add_const]
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  refine ⟨n, a, b, hcov, hcov', ?_⟩
  have hres' : Tendsto (fun t => (coverResolution (fun i => a t i + 1)
      (fun i => b t i + 1) : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa only [coverResolution_add_const] using hres
  have := tendsto_geometricInterleavingDistance_mapperReeb_pair edgeGraph h02
    (fun v => h02 v + 1) hcov hcov' hres hres'
  rwa [geometricInterleavingDistance_graphPLReebGraph_add_const (G := edgeGraph) (h := h02) 1,
    abs_one, ENNReal.ofReal_one] at this

/-! ## M3. Raised apex, one cover -/

/-- The four-cycle height `h4 = (0, 1, 2, 1)` with vertex `2` raised by `1/8`. -/
def g4 : Fin 4 → ℝ := ![0, 1, 17 / 8, 1]

theorem cycleFine_covers_raised (x : Realization C4) :
    ∃ i, plHeight C4 g4 x ∈ ioo (cycleFineLeft i) (cycleFineRight i) := by
  have hx := plHeight_mem_Icc_of_forall (G := C4) (h := g4) (m := 0) (M := 17 / 8)
    (fun v => by fin_cases v <;> norm_num [g4]) x
  by_cases hlow : plHeight C4 g4 x < 3 / 4
  · exact ⟨0, by change (-1 : ℝ) < _ ∧ _ < 3 / 4; constructor <;> linarith [hx.1]⟩
  · by_cases hmid : plHeight C4 g4 x < 3 / 2
    · exact ⟨1, by change (1 / 2 : ℝ) < _ ∧ _ < 3 / 2; constructor <;> linarith⟩
    · exact ⟨2, by change (5 / 4 : ℝ) < _ ∧ _ < 3; constructor <;> linarith [hx.2]⟩

private theorem sup'_h4 : Finset.univ.sup' Finset.univ_nonempty h4 = 2 :=
  le_antisymm (Finset.sup'_le _ _ fun v _ => by fin_cases v <;> norm_num [h4])
    (le_trans (le_of_eq (by simp [h4])) (Finset.le_sup' h4 (Finset.mem_univ (2 : Fin 4))))

private theorem sup'_g4 : Finset.univ.sup' Finset.univ_nonempty g4 = 17 / 8 :=
  le_antisymm (Finset.sup'_le _ _ fun v _ => by fin_cases v <;> norm_num [g4])
    (le_trans (le_of_eq (by simp [g4])) (Finset.le_sup' g4 (Finset.mem_univ (2 : Fin 4))))

/-- Upper bound `2 res + 1/8` for the raised apex. -/
theorem raised_apex_le :
    RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction C4 h4 cycleFineLeft cycleFineRight)
        (graphPLMapperReconstruction C4 g4 cycleFineLeft cycleFineRight) ≤
      2 * (coverResolution cycleFineLeft cycleFineRight : ℝ≥0∞) + ((1 / 8 : ℝ≥0) : ℝ≥0∞) :=
  (geometricInterleavingDistance_mapperReeb_le_add C4 h4 g4 cycleFine_covers
    cycleFine_covers_raised (ε := 1 / 8) fun v => by
      fin_cases v <;> norm_num [h4, g4]).trans_eq (by ring)

/-- Lower bound `1/8 - 2 res` for the raised apex. -/
theorem raised_apex_ge :
    ENNReal.ofReal (1 / 8) ≤
      RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction C4 h4 cycleFineLeft cycleFineRight)
        (graphPLMapperReconstruction C4 g4 cycleFineLeft cycleFineRight) +
      2 * (coverResolution cycleFineLeft cycleFineRight : ℝ≥0∞) := by
  have := ofReal_abs_sup'_sub_le_geometricInterleavingDistance_mapperReeb_add C4 h4 g4
    cycleFine_covers cycleFine_covers_raised
  rw [sup'_h4, sup'_g4, show |(2 : ℝ) - 17 / 8| = 1 / 8 by norm_num [abs_of_neg]] at this
  exact this.trans_eq (by ring)

/-! ## M4. Two disjoint edges -/

private theorem sup'_twoEdgesHeight :
    Finset.univ.sup' Finset.univ_nonempty twoEdgesHeight = 1 :=
  le_antisymm (Finset.sup'_le _ _ fun p _ => by
      rcases p with ⟨_ | _, _ | _⟩ <;> norm_num [twoEdgesHeight])
    (le_trans (le_of_eq (by simp [twoEdgesHeight]))
      (Finset.le_sup' twoEdgesHeight (Finset.mem_univ ((false, true) : Bool × Bool))))

private theorem sup'_twoEdgesRaised :
    Finset.univ.sup' Finset.univ_nonempty twoEdgesRaised = 2 :=
  le_antisymm (Finset.sup'_le _ _ fun p _ => by
      rcases p with ⟨_ | _, _ | _⟩ <;> norm_num [twoEdgesRaised, twoEdgesHeight])
    (le_trans (le_of_eq (by norm_num [twoEdgesRaised, twoEdgesHeight]))
      (Finset.le_sup' twoEdgesRaised (Finset.mem_univ ((true, true) : Bool × Bool))))

/-- On two disjoint edges any covering covers satisfy the maximal-height lower bound `1`. -/
theorem twoEdges_lower_bound {ι ι' : Type} [Finite ι] [Finite ι'] (a b : ι → ℝ)
    (a' b' : ι' → ℝ) (hcov : ∀ x, ∃ i, plHeight twoEdges twoEdgesHeight x ∈ ioo (a i) (b i))
    (hcov' : ∀ x, ∃ i, plHeight twoEdges twoEdgesRaised x ∈ ioo (a' i) (b' i)) :
    ¬ twoEdges.Connected ∧
      ENNReal.ofReal 1 ≤ RGraph.geometricInterleavingDistance
        (graphPLMapperReconstruction twoEdges twoEdgesHeight a b)
        (graphPLMapperReconstruction twoEdges twoEdgesRaised a' b') +
        (coverResolution a b : ℝ≥0∞) + coverResolution a' b' := by
  refine ⟨fun hc => Bool.false_ne_true
    (fst_eq_of_reachable (hc.preconnected (false, false) (true, false))), ?_⟩
  have := ofReal_abs_sup'_sub_le_geometricInterleavingDistance_mapperReeb_add twoEdges
    twoEdgesHeight twoEdgesRaised hcov hcov'
  rwa [sup'_twoEdgesHeight, sup'_twoEdgesRaised,
    show |(1 : ℝ) - 2| = 1 by norm_num [abs_of_neg]] at this

/-! ## M5. The coverage hypothesis -/

/-- The empty cover reconstructs the empty graph. -/
theorem isEmpty_graphPLMapperReconstruction_of_isEmpty_cover {V : Type} [Finite V]
    (G : SimpleGraph V) (h : V → ℝ) {ι : Type} [Finite ι] [IsEmpty ι] (a b : ι → ℝ) :
    IsEmpty (graphPLMapperReconstruction G h a b).obj.left := by
  refine ⟨fun x => ?_⟩
  let t := overBaseMap (graphPLMapperReconstruction G h a b).obj x
  let I : OpenInterval := ioo (t - 1) (t + 1)
  have hx : t ∈ I := ⟨by simp, by simp⟩
  have c : ((RGraph.cosheafFunctor.obj (graphPLMapperReconstruction G h a b)).obj).obj I :=
    ZerothHomotopy.mk ⟨x, hx⟩
  have d := (categoricalMapperReconstructionIso (plHeight G h) a b
    (fun i => finite_zerothHomotopy G h (ioo (a i) (b i)))).hom.app I c
  induction d using ZerothHomotopy.rec with
  | mk y =>
    obtain ⟨i, -⟩ := mem_coverSaturation.mp y.2
    exact isEmptyElim i

/-- With the empty cover of a nonempty graph the reconstruction is at distance `⊤` from the Reeb
quotient, although the cover resolution is `0`. -/
theorem empty_cover_distance_top {V : Type} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (h : V → ℝ) (a b : Empty → ℝ) :
    coverResolution a b = 0 ∧
      RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (graphPLReebGraph G h) = ⊤ := by
  refine ⟨?_, ?_⟩
  · unfold coverResolution
    simp
  · refine RGraph.geometricInterleavingDistance_eq_top_of_isEmpty_of_nonempty
      (isEmpty_graphPLMapperReconstruction_of_isEmpty_cover G h a b) ?_
    rw [← RGraph.heightRange_nonempty_iff, heightRange_graphPLReebGraph]
    exact range_nonempty_iff_nonempty.2 ⟨vertex G (Classical.arbitrary V)⟩

/-! ## M6. The empty vertex type -/

/-- On an empty vertex type every Mapper reconstruction is empty, and the Mapper and Reeb
distances are `0`. -/
theorem empty_vertex_type {ι ι' : Type} [Finite ι] [Finite ι'] (G : SimpleGraph Empty)
    (h g : Empty → ℝ) (a b : ι → ℝ) (a' b' : ι' → ℝ) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
        (graphPLMapperReconstruction G g a' b') = 0 ∧
      RGraph.geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) = 0 := by
  refine ⟨?_, geometricInterleavingDistance_graphPLReebGraph_of_isEmpty (G := G) h g⟩
  have hE : IsEmpty (Realization G) :=
    ⟨fun x => by
      induction x using TDA.Reeb.GraphRealization.ind with
      | vertex v => exact isEmptyElim v
      | edgePoint d t => exact isEmptyElim d.fst⟩
  rw [geometricInterleavingDistance_graphPLMapperReconstruction_eq]
  have e1 : ∀ I, IsEmpty ((coverComponents (plHeight G h) (fun i => ioo (a i) (b i))).obj I) :=
    fun I => componentFunctor_obj_isEmpty_of_isEmpty _ _
  have e2 : ∀ I, IsEmpty ((coverComponents (plHeight G g) (fun i => ioo (a' i) (b' i))).obj I) :=
    fun I => componentFunctor_obj_isEmpty_of_isEmpty _ _
  refine interleavingDistance_eq_zero_of_iso (NatIso.ofComponents
    (fun I => haveI := e1 I; haveI := e2 I; (Equiv.equivOfIsEmpty _ _).toIso) fun _ => ?_)
  ext c
  exact (e1 _).elim c

/-! ## M7. The cosheaf route -/

/-- The geometric upper bound of the Mapper reconstructions follows from the cosheaf-level bound
through the identification of the reconstruction distance with the assembled interleaving
distance. -/
theorem upper_bound_via_cosheaf {ι ι' : Type} [Finite ι] [Finite ι'] {V : Type} [Fintype V]
    (G : SimpleGraph V) (h g : V → ℝ) (a b : ι → ℝ) (a' b' : ι' → ℝ)
    (hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i))
    (hcov' : ∀ x, ∃ i, plHeight G g x ∈ ioo (a' i) (b' i)) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') ≤
      (coverResolution a b : ℝ≥0∞) + edist h g + coverResolution a' b' := by
  rw [geometricInterleavingDistance_graphPLMapperReconstruction_eq]
  have := interleavingDistance_coverComponents_le_add_edist (f := plHeight G h)
    (g := plHeight G g) (U := fun i => ioo (a i) (b i)) (U' := fun i => ioo (a' i) (b' i))
    hcov (diameter_le_coverResolution a b) hcov' (diameter_le_coverResolution a' b')
  rwa [edist_ofFun_plHeight_eq_edist] at this

end

end TDA.Mapper.MapperReebPerturbationExamples
