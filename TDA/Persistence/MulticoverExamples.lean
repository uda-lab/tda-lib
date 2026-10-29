import TDA.Persistence.GromovProkhorovMulticover

/-!
# Outlier and cover-nerve examples

The metric example adds one point at an arbitrary nonzero distance and obtains
the half-mass GP bound. The cover example distinguishes its nerve from the
normalized flag complex: the comparison is an inclusion, not equality of faces.
-/

set_option autoImplicit false
open scoped NNReal ENNReal
namespace TDA.Persistence.MulticoverExamples
open MeasureTheory Metric
open TDA.Topology.MeasureBifiltration TDA.Topology.FiniteGromovProkhorov
open TDA.Filtration.SubdivisionRips

private def outlierPosition (L : ℝ) (v : Fin 2) : ℝ := if v = 0 then 0 else L

private theorem outlierPosition_injective {L : ℝ} (hL : L ≠ 0) :
    Function.Injective (outlierPosition L) := by
  intro v w h
  fin_cases v <;> fin_cases w <;> simp_all [outlierPosition]

@[instance_reducible]
private noncomputable def outlierMetric {L : ℝ} (hL : L ≠ 0) : MetricSpace (Fin 2) :=
  MetricSpace.induced (outlierPosition L) (outlierPosition_injective hL) (inferInstance : MetricSpace ℝ)

private def origin : Unit ↪ Fin 2 := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

/-- The new point is truly at distance `|L|` from the original point. -/
theorem added_point_distance {L : ℝ} (hL : L ≠ 0) :
    let : MetricSpace (Fin 2) := outlierMetric hL
    dist (0 : Fin 2) 1 = |L| := by
  change dist (outlierPosition L 0) (outlierPosition L 1) = |L|
  simp [outlierPosition, Real.dist_eq]

/-- One arbitrarily far new point costs at most one half in actual GP distance. -/
theorem arbitrary_outlier_gp_le_half {L : ℝ} (hL : L ≠ 0) :
    let : MetricSpace (Fin 2) := outlierMetric hL
    gromovProkhorovEDist Unit (Fin 2) ≤ ENNReal.ofReal (1 / 2) := by
  let : MetricSpace (Fin 2) := outlierMetric hL
  have hi : Isometry origin := Isometry.of_dist_eq (fun _ _ => by simp [origin])
  have h := gromovProkhorovEDist_embedding_le origin hi
  norm_num at h
  exact h

/-- The half-mass GP estimate supplies the actual finite sup-norm witness
at three quarters, including the spatial interleaving and both SR homology maps. -/
noncomputable def outlierWitness {L : ℝ} (hL : L ≠ 0) :
    letI := outlierMetric hL
    SupNormWitness Unit (Fin 2) (3 / 4) := by
  let : MetricSpace (Fin 2) := outlierMetric hL
  apply supNormWitness (3 / 4)
  apply (arbitrary_outlier_gp_le_half hL).trans_lt
  exact (ENNReal.ofReal_lt_coe_iff (by norm_num : 0 ≤ (1 / 2 : ℝ))).2 (by norm_num)

private noncomputable def halfIndex : Index :=
  ⟨OrderDual.toDual ⟨1 / 2, by norm_num⟩, ⟨2, by norm_num⟩⟩

private def points (v : Fin 2) : ℝ := v.val

private def incomparablePair : Finset (Finset (Fin 2)) := {{0}, {1}}

/-- The large-face nerve has the edge between the two singleton labels,
whose open balls overlap. -/
theorem incomparable_pair_mem_cover_nerve :
    incomparablePair ∈ TDA.Topology.nerve (largeFaceCover points halfIndex) := by
  apply (mem_largeFaceNerve_iff points halfIndex incomparablePair).2
  refine ⟨by simp [incomparablePair], ?_, ?_⟩
  · intro s hs
    simp only [incomparablePair, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    all_goals
      constructor
      · refine ⟨by simp, (0 : ℝ), ?_⟩
        intro v hv
        simp only [Finset.mem_singleton] at hv
        subst v
        norm_num [points, halfIndex, radius]
      · norm_num [halfIndex, mass]
  · refine ⟨?_, (0 : ℝ), ?_⟩
    · simp [incomparablePair]
    · intro v hv
      fin_cases v <;> norm_num [points, halfIndex, radius]

/-- The same pair is absent from the normalized subdivision because its
members are incomparable, so the nerve comparison cannot be a face equality. -/
theorem incomparable_pair_not_mem_flag :
    incomparablePair ∉ subdivision (openCech points (radius halfIndex)) (mass halfIndex) := by
  intro h
  have hc := h.2.2 ({0} : Finset (Fin 2)) (by simp [incomparablePair])
    ({1} : Finset (Fin 2)) (by simp [incomparablePair])
  rcases hc with h | h
  · have := h (by simp : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)))
    norm_num at this
  · have := h (by simp : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)))
    norm_num at this

end TDA.Persistence.MulticoverExamples
