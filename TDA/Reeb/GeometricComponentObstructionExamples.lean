import TDA.Reeb.GeometricComponentObstruction
import TDA.Reeb.GeometricDistanceBoundsExamples

/-!
# Fixtures for interval-local component obstructions

This module records the interval-local values and distance consequences for the parallel-edge
loop, the single edge, and two disjoint edges.  It also records the sharp threshold at `1 / 4`,
the boundary where the injectivity hypothesis is unavailable, and the independent midpoint and
two-segment controls.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.GeometricComponentObstruction

open OpenInterval CylinderPresentation FiniteReebData RGraph
open TDA.Reeb.Examples.Cylinder
  (S01 S01_value_zero S01_value_one parallelData twoSegData twoSegLabel)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (parallelGraph singleGraph)
open TDA.Reeb.Examples.RGraphSmoothing (subsingleton_of_one_edge twoSegGraph)
open TDA.Reeb.Examples.GeometricInterleaving (coe_quarter_ennreal)
open TDA.Reeb.Examples.GeometricDistanceBounds
  (hausdorffEDist_heightRange_parallel_single)
open TDA.Reeb.Examples.ConstructibleSmoothing (quarter coe_quarter)
open TDA.Reeb.Examples.QuotientThickeningAddition (eighth)
open TDA.Reeb.RGraph.Examples (singleEdge)

/-- The restriction of the parallel-edge value is bijective inside its open gap. -/
theorem parallel_restrict_bijective {I J : OpenInterval} (hIJ : I ≤ J)
    (hJ : J ≤ S01.K 0) (hI : (I : Set ℝ).Nonempty) :
    Function.Bijective ((cosheafFunctor.obj parallelGraph).obj.map (homOfLE hIJ)) := by
  change Function.Bijective ((parallelData.toCosheaf S01).map (homOfLE hIJ))
  apply (parallelData.toCosheaf_isConstructibleAt S01).bijective hIJ hI
  intro i
  exact iff_of_false
    (fun hi => S01.value_notMem_K 0 i
      (OpenInterval.le_iff_subset.1 (hIJ.trans hJ) hi))
    (fun hi => S01.value_notMem_K 0 i (OpenInterval.le_iff_subset.1 hJ hi))

/-- Every nonempty interval contained in the parallel-edge gap has a nontrivial value. -/
theorem parallel_nontrivial_of_le_K {I : OpenInterval} (hI : I ≤ S01.K 0)
    (hI_nonempty : (I : Set ℝ).Nonempty) :
    Nontrivial ((cosheafFunctor.obj parallelGraph).obj.obj I) := by
  change Nontrivial ((parallelData.toCosheaf S01).obj I)
  have hK : Nontrivial ((parallelData.toCosheaf S01).obj (S01.K 0)) :=
    @Function.Injective.nontrivial _ _ (inferInstanceAs (Nontrivial Bool)) _
      (parallelData.edgeLabel S01 0).injective
  exact @Function.Surjective.nontrivial _ _ hK _
    (parallel_restrict_bijective hI le_rfl hI_nonempty).surjective

/-- Every value of the single-edge cosheaf is a subsingleton. -/
theorem single_subsingleton (L : OpenInterval) :
    Subsingleton ((cosheafFunctor.obj singleGraph).obj.obj L) := by
  change Subsingleton ((singleEdge.toCosheaf S01).obj L)
  exact subsingleton_of_one_edge singleEdge (inferInstanceAs (Subsingleton Unit))
    (inferInstanceAs (Subsingleton Unit)) (inferInstanceAs (Subsingleton Unit)) () L

/-- The interval used by the sharp parallel-edge obstruction. -/
def obstructionInterval (ε : ℝ≥0) : OpenInterval :=
  ioo (2 * (ε : ℝ)) (1 - 2 * (ε : ℝ))

/-- The double thickening of the obstruction interval is the open gap below `1 / 4`. -/
theorem thicken_thicken_obstructionInterval {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 4) :
    thicken ε (thicken ε (obstructionInterval ε)) = S01.K 0 := by
  ext x
  rw [obstructionInterval, thicken_ioo (by linarith) ε,
    thicken_ioo (by linarith) ε, S01.mem_K, mem_ioo]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
  constructor
  · rintro ⟨hx, hy⟩
    constructor <;> linarith
  · rintro ⟨hx, hy⟩
    constructor <;> linarith

/-- The obstruction interval is nonempty below `1 / 4`. -/
theorem obstructionInterval_nonempty {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 4) :
    ((obstructionInterval ε : OpenInterval) : Set ℝ).Nonempty := by
  refine ⟨1 / 2, ?_⟩
  show (1 / 2 : ℝ) ∈ ioo (2 * (ε : ℝ)) (1 - 2 * (ε : ℝ))
  exact mem_ioo.2 ⟨by linarith, by linarith⟩

/-- No geometric interleaving exists below `1 / 4` from the parallel-edge loop to the single edge.
-/
theorem parallelSingle_isEmpty {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 4) :
    IsEmpty (GeometricInterleaving ε parallelGraph singleGraph) := by
  let I : OpenInterval := obstructionInterval ε
  have hI : (I : Set ℝ).Nonempty := obstructionInterval_nonempty hε
  have hdouble : thicken ε (thicken ε I) ≤ S01.K 0 := by
    exact (thicken_thicken_obstructionInterval hε).le
  have hIJ : I ≤ thicken ε (thicken ε I) :=
    (le_thicken ε I).trans (le_thicken ε (thicken ε I))
  have hmap : Function.Injective ((cosheafFunctor.obj parallelGraph).obj.map
      (homOfLE hIJ)) :=
    (parallel_restrict_bijective hIJ hdouble hI).injective
  have hnontrivial : Nontrivial ((cosheafFunctor.obj parallelGraph).obj.obj I) :=
    parallel_nontrivial_of_le_K
      ((le_thicken ε I).trans ((le_thicken ε (thicken ε I)).trans hdouble)) hI
  have hsubsingleton : Subsingleton
      ((cosheafFunctor.obj singleGraph).obj.obj (thicken ε I)) :=
    single_subsingleton _
  exact @isEmpty_geometricInterleaving_of_injective_of_subsingleton ε parallelGraph
    singleGraph I hmap hnontrivial hsubsingleton

/-- No geometric interleaving exists below `1 / 4` in the reverse direction either. -/
theorem singleParallel_isEmpty {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 4) :
    IsEmpty (GeometricInterleaving ε singleGraph parallelGraph) := by
  refine ⟨fun i => ?_⟩
  exact (parallelSingle_isEmpty hε).false i.symm

/-- The geometric interleaving distance of the parallel-edge loop and the single edge is `1 / 4`.
-/
theorem geometricInterleavingDistance_parallel_single :
    geometricInterleavingDistance parallelGraph singleGraph = 1 / 4 := by
  apply le_antisymm
  · exact TDA.Reeb.Examples.GeometricInterleaving.geometricInterleavingDistance_parallel_single_le
  · rw [← coe_quarter_ennreal]
    apply le_geometricInterleavingDistance_of_isEmpty
    intro ε hε
    apply parallelSingle_isEmpty
    have hε' : (ε : ℝ) < (quarter : ℝ) := by exact_mod_cast hε
    simpa only [coe_quarter] using hε'

/-- The corresponding cosheaf interleaving distance is also `1 / 4`. -/
theorem interleavingDistance_parallel_single :
    interleavingDistance (cosheafFunctor.obj parallelGraph).obj
      (cosheafFunctor.obj singleGraph).obj = 1 / 4 := by
  rw [← geometricInterleavingDistance_eq_interleavingDistance parallelGraph singleGraph]
  exact geometricInterleavingDistance_parallel_single

/-- The parallel-edge and single-edge geometric distance is positive. -/
theorem geometricInterleavingDistance_parallel_single_pos :
    0 < geometricInterleavingDistance parallelGraph singleGraph := by
  rw [geometricInterleavingDistance_parallel_single]
  norm_num

/-- The height-range lower bound is strict for the parallel-edge and single-edge pair. -/
theorem hausdorffEDist_heightRange_parallel_single_lt :
    Metric.hausdorffEDist (heightRange parallelGraph) (heightRange singleGraph) <
      geometricInterleavingDistance parallelGraph singleGraph := by
  rw [hausdorffEDist_heightRange_parallel_single]
  exact geometricInterleavingDistance_parallel_single_pos

/-- The interval-local obstruction rules out every geometric `1 / 8`-interleaving.  Its interval
is `ioo (1 / 4) (3 / 4)`, which thickens to `ioo (1 / 8) (7 / 8)` and then to `ioo 0 1`. -/
theorem parallelSingle_eighth_isEmpty :
    IsEmpty (GeometricInterleaving eighth parallelGraph singleGraph) := by
  apply parallelSingle_isEmpty
  show (1 / 8 : ℝ) < 1 / 4
  norm_num

/-- The parameter `e24` is `6 / 25`, i.e. `0.24`. -/
def e24 : ℝ≥0 := ⟨6 / 25, by norm_num⟩

/-- The interval-local obstruction at `0.24`, using `I = ioo (12 / 25) (13 / 25)`,
rules out every geometric `e24`-interleaving of the parallel-edge and single-edge pair. -/
theorem parallelSingle_e24_isEmpty :
    IsEmpty (GeometricInterleaving e24 parallelGraph singleGraph) := by
  apply parallelSingle_isEmpty
  change (6 / 25 : ℝ) < 1 / 4
  norm_num

/-- At `ε = 1 / 4`, no nonempty interval has its double thickening contained in the open gap,
so the obstruction's injectivity hypothesis is unavailable, consistently with
`parallelSingleInterleaving`. -/
theorem thicken_half_not_le_K :
    ∀ I : OpenInterval, (I : Set ℝ).Nonempty →
      ¬ thicken (quarter + quarter) I ≤ S01.K 0 := by
  intro I hI hle
  obtain ⟨x, hx⟩ := hI
  have hhalf : ((quarter + quarter : ℝ≥0) : ℝ) = 1 / 2 := by
    rw [NNReal.coe_add, coe_quarter]
    norm_num
  have hleft : x - (1 / 2 : ℝ) ∈ S01.K 0 := by
    apply hle
    rw [mem_thicken]
    refine ⟨x, hx, ?_⟩
    have hx' : (x - (1 / 2 : ℝ)) - x = -(1 / 2 : ℝ) := by ring
    rw [hx', abs_of_nonpos (by norm_num), hhalf]
    norm_num
  have hright : x + (1 / 2 : ℝ) ∈ S01.K 0 := by
    apply hle
    rw [mem_thicken]
    refine ⟨x, hx, ?_⟩
    have hx' : (x + (1 / 2 : ℝ)) - x = (1 / 2 : ℝ) := by ring
    rw [hx', abs_of_nonneg (by norm_num), hhalf]
  rw [S01.mem_K] at hleft hright
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
    at hleft hright
  linarith [hleft.1, hright.2]

/-- The subsingleton (nontriviality) form of the local component obstruction never applies with
the single edge as source, because every single-edge value is a subsingleton.  The positive
edge--midpoint distance below `1 / 2` (`edgeMid_isEmpty`) comes from the range bound.  This lemma
does not exclude the cardinality form: an empty midpoint value can be smaller than a one-point
edge value. -/
theorem edgeMid_obstruction_unavailable :
    ∀ I : OpenInterval,
      ¬ Nontrivial ((cosheafFunctor.obj singleGraph).obj.obj I) := by
  intro I
  exact not_nontrivial_iff_subsingleton.mpr (single_subsingleton I)

/-- The two disjoint edges and the single edge have infinite geometric interleaving distance. -/
theorem geometricInterleavingDistance_twoSeg_single :
    geometricInterleavingDistance twoSegGraph singleGraph = ⊤ := by
  rw [geometricInterleavingDistance_eq_top_iff]
  intro ε
  have hmap : Function.Injective ((cosheafFunctor.obj twoSegGraph).obj.map
      (homOfLE ((le_thicken ε (⊤ : OpenInterval)).trans
        (le_thicken ε (thicken ε (⊤ : OpenInterval)))))) := by
    have hmap_of_eq {J : OpenInterval} (hJ : J = ⊤)
        (h : (⊤ : OpenInterval) ≤ J) :
        Function.Injective
          ((cosheafFunctor.obj twoSegGraph).obj.map (homOfLE h)) := by
      subst J
      rw [map_eq_map_of_interval (cosheafFunctor.obj twoSegGraph).obj _ (𝟙 _),
        CategoryTheory.Functor.map_id]
      exact Function.injective_id
    exact hmap_of_eq (J := thicken ε (thicken ε (⊤ : OpenInterval)))
      (by simp only [thicken_top])
      ((le_thicken ε (⊤ : OpenInterval)).trans
        (le_thicken ε (thicken ε (⊤ : OpenInterval))))
  have hnontrivial : Nontrivial
      ((cosheafFunctor.obj twoSegGraph).obj.obj (⊤ : OpenInterval)) := by
    change Nontrivial ((intervalComponents (overBaseMap twoSegGraph.obj)).obj ⊤)
    let c (b : Bool) :
        (intervalComponents (overBaseMap twoSegGraph.obj)).obj ⊤ :=
      ZerothHomotopy.mk
        ⟨(ofFiniteData twoSegData).ofVertex S01 0 b, Set.mem_univ _⟩
    refine ⟨⟨c false, c true, ?_⟩⟩
    intro h
    dsimp [c] at h
    have hc : Continuous fun x :
        {x : (ofFiniteData twoSegData).Realization S01 //
          (ofFiniteData twoSegData).height S01 x ∈ (⊤ : OpenInterval)} =>
        twoSegLabel x.1 :=
      twoSegLabel.continuous.comp continuous_subtype_val
    have hj := (Quotient.exact h).map hc
    exact Bool.false_ne_true (joined_eq_of_discrete hj)
  have hsubsingleton : Subsingleton
      ((cosheafFunctor.obj singleGraph).obj.obj
        (thicken ε (⊤ : OpenInterval))) := by
    exact single_subsingleton _
  exact @isEmpty_geometricInterleaving_of_injective_of_subsingleton ε twoSegGraph
    singleGraph (⊤ : OpenInterval) hmap hnontrivial hsubsingleton

/-- The reverse `1 / 8` obstruction follows by symmetry. -/
theorem singleParallel_eighth_isEmpty :
    IsEmpty (GeometricInterleaving eighth singleGraph parallelGraph) :=
  singleParallel_isEmpty (by
    show (1 / 8 : ℝ) < 1 / 4
    norm_num)

/-- The strict height-range gap is recorded as a named parallel-edge fixture. -/
theorem parallel_single_range_bound_strict :
    Metric.hausdorffEDist (heightRange parallelGraph) (heightRange singleGraph) <
      geometricInterleavingDistance parallelGraph singleGraph :=
  hausdorffEDist_heightRange_parallel_single_lt

end Examples.GeometricComponentObstruction

end

end TDA.Reeb
