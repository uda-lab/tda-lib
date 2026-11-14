import TDA.Mapper.GraphPLReebMapPair
import TDA.Mapper.GraphPLReebExtremal
import TDA.Reeb.GraphRealizationExamples
import TDA.Reeb.GraphPLVertexPerturbationExamples
import TDA.Reeb.ComponentsExamples
import TDA.Reeb.InterleavingCardinality
import TDA.Mapper.PullbackCoverExamples

/-!
# Fixtures for height-controlled map pairs

The fixtures include an interval collapsing to a point, the exact distance from an edge of height
range `[0, 1]` to a point at height `1/2`, recovery of the fixed-space perturbation interleaving,
and a discrete two-point to one-point negative control.

The edge-to-point data are shared with the centred and capped Mapper map-pair fixtures: the
path-connectedness of `unitInterval` and of the edge realization, the heights `edgeHeight` and
`pointHeight`, the constant maps `edgeToPoint` and `pointToEdge`, their height lemmas and the
`1/2` map pair `edgePointPair`. The negative control uses `TDA.Mapper.Examples.boolToUnit`. -/

open Set TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Mapper.GraphPL
open TDA.Reeb.RGraph
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ half pointGraph edgeHomeomorph)
open TDA.Reeb.Examples.GraphPLVertexPerturbation (flat tilted)
open TDA.Mapper.Examples (boolToUnit)
open scoped NNReal ENNReal

namespace TDA.Mapper.GraphPL.Examples.HeightMapPair

noncomputable section

/-- The unit interval is path-connected, by convexity. -/
instance unitIntervalPathConnectedSpace : PathConnectedSpace unitInterval := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  exact (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩

/-- The realization of the single edge is path-connected, through its homeomorphism with the
unit interval. -/
instance edgeRealizationPathConnectedSpace : PathConnectedSpace (Realization edgeGraph) :=
  edgeHomeomorph.symm.surjective.pathConnectedSpace edgeHomeomorph.symm.continuous

/-- Every point of the one-point realization is its vertex. -/
theorem pointRealization_eq (x : Realization pointGraph) :
    x = vertex pointGraph () := Subsingleton.elim _ _

/-! ### Interval to point -/

private def zeroInterval : C(unitInterval, ℝ) := ContinuousMap.const _ 0

private def zeroUnit : C(Unit, ℝ) := ContinuousMap.const Unit 0

private def intervalToUnit : C(unitInterval, Unit) := ContinuousMap.const _ ()

private def unitToZero : C(Unit, unitInterval) := ContinuousMap.const _ (0 : unitInterval)

private def intervalPointPair : HeightMapPair zeroInterval zeroUnit 0 where
  φ := intervalToUnit
  ψ := unitToZero
  hφ x := by simp [zeroInterval, zeroUnit]
  hψ x := by simp [zeroInterval, zeroUnit]
  hψφ x := by
    refine ⟨PathConnectedSpace.somePath x 0, ?_⟩
    intro t
    simp [zeroInterval]
  hφψ _ := by
    refine ⟨Path.refl (), ?_⟩
    intro t
    simp [zeroUnit]

/-- The zero-height interval-to-point pair gives distance zero, although the composite on the
interval is constant rather than the identity. -/
theorem interval_to_point_distance_zero :
    interleavingDistance (intervalComponents zeroInterval) (intervalComponents zeroUnit) = 0 := by
  apply le_antisymm
  · exact intervalPointPair.interleavingDistance_le
  · exact bot_le

/-! ### Edge to point -/

/-- The PL height of the single edge with endpoint heights `0` and `1`. -/
def edgeHeight : C(Realization edgeGraph, ℝ) := plHeight edgeGraph tilted

/-- The PL height of the point at height `1/2`. -/
def pointHeight : C(Realization pointGraph, ℝ) :=
  plHeight pointGraph (fun _ => (1 / 2 : ℝ))

/-- The constant map from the edge to the point. -/
def edgeToPoint : C(Realization edgeGraph, Realization pointGraph) :=
  ContinuousMap.const _ (vertex pointGraph ())

/-- The constant map from the point to the midpoint of the edge. -/
def pointToEdge : C(Realization pointGraph, Realization edgeGraph) :=
  ContinuousMap.const _ (edgePoint edgeGraph d₀ half)

/-- The edge height takes values in `[0, 1]`. -/
theorem edgeHeight_mem_Icc (x : Realization edgeGraph) :
    edgeHeight x ∈ Icc (0 : ℝ) 1 :=
  plHeight_mem_Icc_of_forall (m := 0) (M := 1)
    (fun b => by cases b <;> norm_num [tilted]) x

/-- The midpoint of the edge has height `1/2`. -/
theorem edgeMidpoint_height : edgeHeight (edgePoint edgeGraph d₀ half) = 1 / 2 := by
  simp [edgeHeight, GraphPL.plHeight_edgePoint, GraphPL.dartHeight, tilted, d₀, half]

/-- The point height is `1/2` everywhere. -/
theorem pointHeight_apply (x : Realization pointGraph) : pointHeight x = 1 / 2 := by
  rw [pointRealization_eq x]
  simp [pointHeight]

/-- The constant maps between the edge and the point form a height-map pair with parameter
`1/2`. -/
def edgePointPair : HeightMapPair edgeHeight pointHeight (1 / 2 : ℝ≥0) where
  φ := edgeToPoint
  ψ := pointToEdge
  hφ x := by
    rw [pointHeight_apply]
    change |(1 / 2 : ℝ) - edgeHeight x| ≤ 1 / 2
    rw [abs_le]
    have hx := edgeHeight_mem_Icc x
    constructor <;> linarith [hx.1, hx.2]
  hψ x := by
    change |edgeHeight (edgePoint edgeGraph d₀ half) - pointHeight x| ≤ 1 / 2
    rw [edgeMidpoint_height, pointHeight_apply]
    norm_num
  hψφ x := by
    let γ : Path x (pointToEdge (edgeToPoint x)) := by
      simpa [pointToEdge, edgeToPoint] using
        (PathConnectedSpace.somePath x (edgePoint edgeGraph d₀ half))
    refine ⟨γ, ?_⟩
    intro t
    have h₁ := edgeHeight_mem_Icc (γ t)
    have h₂ := edgeHeight_mem_Icc x
    change |edgeHeight (γ t) - edgeHeight x| ≤ _
    rw [abs_le]
    have hsum : ((1 / 2 : ℝ≥0) : ℝ) + ((1 / 2 : ℝ≥0) : ℝ) = 1 := by norm_num
    rw [hsum]
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  hφψ x := by
    rw [pointRealization_eq x]
    refine ⟨Path.refl _, ?_⟩
    intro t
    change |pointHeight (vertex pointGraph ()) - pointHeight (vertex pointGraph ())| ≤
      ((1 / 2 : ℝ≥0) + (1 / 2 : ℝ≥0) : ℝ≥0)
    rw [sub_self, abs_zero]
    norm_num

/-- The exact edge-to-point distance is `1/2`. The map-pair theorem gives the upper bound, and
the supremum of the height ranges gives the matching lower bound. -/
theorem edge_to_point_distance_eq_half :
    geometricInterleavingDistance (graphPLReebGraph edgeGraph tilted)
      (graphPLReebGraph pointGraph fun _ => (1 / 2 : ℝ)) = (1 / 2 : ℝ≥0∞) := by
  have hup := geometricInterleavingDistance_graphPLReebGraph_le_of_heightMapPair edgePointPair
  have hRE : (heightRange (graphPLReebGraph edgeGraph tilted)).Nonempty := by
    rw [heightRange_graphPLReebGraph]
    exact range_nonempty_iff_nonempty.mpr ⟨vertex edgeGraph false⟩
  have hRP : (heightRange (graphPLReebGraph pointGraph fun _ => (1 / 2 : ℝ))).Nonempty := by
    rw [heightRange_graphPLReebGraph]
    exact range_nonempty_iff_nonempty.mpr ⟨vertex pointGraph ()⟩
  have hlow := ofReal_abs_sSup_sub_le_hausdorffEDist hRE hRP
    (bddAbove_heightRange _) (bddAbove_heightRange _)
  have hs₁ : Finset.univ.sup' Finset.univ_nonempty tilted = 1 := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun b _ => by cases b <;> norm_num [tilted])
    · simp [tilted]
  have hs₂ : Finset.univ.sup' Finset.univ_nonempty (fun _ : Unit => (1 / 2 : ℝ)) = 1 / 2 := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun _ _ => le_rfl)
    · simp
  rw [heightRange_graphPLReebGraph, heightRange_graphPLReebGraph,
    sSup_range_plHeight, sSup_range_plHeight] at hlow
  rw [hs₁, hs₂] at hlow
  have hdist := hausdorffEDist_heightRange_le_geometricInterleavingDistance
    (graphPLReebGraph edgeGraph tilted)
    (graphPLReebGraph pointGraph fun _ => (1 / 2 : ℝ))
  rw [heightRange_graphPLReebGraph, heightRange_graphPLReebGraph] at hdist
  have hlow' := hlow.trans hdist
  have habs : |(1 : ℝ) - (1 / 2 : ℝ)| = (1 / 2 : ℝ) := by norm_num
  rw [habs] at hlow'
  have hval : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℝ≥0) : ℝ) by norm_num]
    simp
  rw [hval] at hlow'
  have hlow'' : (1 / 2 : ℝ≥0∞) ≤
      geometricInterleavingDistance (graphPLReebGraph edgeGraph tilted)
        (graphPLReebGraph pointGraph fun _ => (1 / 2 : ℝ)) := hlow'
  have hup' : geometricInterleavingDistance (graphPLReebGraph edgeGraph tilted)
      (graphPLReebGraph pointGraph fun _ => (1 / 2 : ℝ)) ≤ (1 / 2 : ℝ≥0∞) := by
    simpa using hup
  exact le_antisymm hup' hlow''

/-! ### Fixed-space recovery -/

private theorem edgeHeight_perturbation_bound (x : Realization edgeGraph) :
    |plHeight edgeGraph tilted x - plHeight edgeGraph flat x| ≤ ((1 : ℝ≥0) : ℝ) :=
  abs_plHeight_sub_le edgeGraph (fun b => by cases b <;> norm_num [tilted, flat]) x

/-- On the single edge, the identity-map pair induces the existing perturbation interleaving. -/
theorem edge_pair_recovers_perturbation :
    (HeightMapPair.ofUniformBound edgeHeight_perturbation_bound).interleaving =
      perturbationInterleaving edgeHeight_perturbation_bound :=
  HeightMapPair.interleaving_eq_perturbationInterleaving edgeHeight_perturbation_bound

/-! ### Discrete negative control -/

private def boolZero : C(Bool, ℝ) := ContinuousMap.const Bool 0

private def unitZero : C(Unit, ℝ) := ContinuousMap.const Unit 0

private def unitToFalse : C(Unit, Bool) := ContinuousMap.const Unit false

private theorem no_path_true_false : ¬ Nonempty (Path (true : Bool) false) := by
  rintro ⟨γ⟩
  have h := TDA.Reeb.Examples.eq_of_joined_of_discrete (⟨γ⟩ : Joined true false)
  exact Bool.noConfusion h

/-- The constant maps `Bool → Unit → Bool` preserve both zero heights exactly, but for every
height bound `r` their composite cannot be joined to the identity at `true`. -/
theorem bool_to_point_path_condition_fails :
    (∀ b, boolZero b = unitZero (boolToUnit b)) ∧
      (∀ x, unitZero x = boolZero (unitToFalse x)) ∧
      ∀ r : ℝ, ¬ ∃ γ : Path (true : Bool) (unitToFalse (boolToUnit true)),
        ∀ t, |boolZero (γ t) - boolZero true| ≤ r := by
  refine ⟨by intro b; simp [boolZero, unitZero, boolToUnit], ?_, ?_⟩
  · intro x
    simp [boolZero, unitZero, unitToFalse]
  · rintro r ⟨γ, _⟩
    exact no_path_true_false ⟨γ⟩

private def boolTopComponentsEquiv : (intervalComponents boolZero).obj ⊤ ≃ Bool where
  toFun := ZerothHomotopy.lift (fun x => x.1)
    (fun _ _ p => congrArg Subtype.val
      (TDA.Reeb.Examples.eq_of_joined_of_discrete ⟨p⟩))
  invFun b := ZerothHomotopy.mk ⟨b, TopologicalSpace.Opens.mem_top _⟩
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  right_inv _ := rfl

private def unitTopComponentsEquiv : (intervalComponents unitZero).obj ⊤ ≃ Unit where
  toFun _ := ()
  invFun _ := ZerothHomotopy.mk ⟨(), TopologicalSpace.Opens.mem_top _⟩
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      have hx : x = ⟨(), TopologicalSpace.Opens.mem_top _⟩ := Subsingleton.elim _ _
      rw [hx]
  right_inv _ := rfl

/-- The constant-height discrete two-point space has distance `⊤` from the one-point space,
detected by their different component counts over `⊤`. -/
theorem bool_to_point_distance_eq_top :
    interleavingDistance (intervalComponents boolZero) (intervalComponents unitZero) = ⊤ := by
  apply interleavingDistance_eq_top_of_card_ne
  have hbool : Nat.card ((intervalComponents boolZero).obj ⊤) = 2 := by
    rw [Nat.card_congr boolTopComponentsEquiv]
    norm_num
  have hunit : Nat.card ((intervalComponents unitZero).obj ⊤) = 1 := by
    rw [Nat.card_congr unitTopComponentsEquiv]
    norm_num
  rw [hbool, hunit]
  norm_num

end

end TDA.Mapper.GraphPL.Examples.HeightMapPair
