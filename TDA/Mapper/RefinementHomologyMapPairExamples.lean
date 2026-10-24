import TDA.Mapper.RefinementHomologyMapPair
import TDA.Mapper.RefinementHomologyInterleavingExamples
import TDA.Mapper.RefinementHomologyLowerBound
import TDA.Mapper.RefinementHomologyDomainMapExamples
import TDA.Mapper.RefinementHomologyEssential
import TDA.Mapper.RefinementHomologyLowerBound
import TDA.Mapper.GraphPLReebMapPairExamples
import TDA.Reeb.GraphRealizationExamples
import TDA.Reeb.GraphPLVertexPerturbationExamples
import TDA.Simplicial.H0Augmentation

/-!
# Fixtures for centred Mapper homology map-pair bounds

The fixed-space perturbation bound is recovered by the map-pair theorem. On the single edge of
heights `0` and `1`, a map pair to a point at height `1/2` gives distance at most `1/2`, although
the degree-zero modules are not isomorphic at radius `1/2`.
-/

namespace TDA.Mapper.RefinementHomologyMapPairExamples

open CategoryTheory
open TDA.Topology TDA.Simplicial TDA.Persistence TDA.Reeb TDA.Reeb.GraphPL
open TDA.Reeb.GraphRealization
open TDA.Reeb.Examples.GraphRealization
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ half pointGraph edgeHomeomorph)
open TDA.Reeb.Examples.GraphPLVertexPerturbation (tilted)
open TDA.Mapper.RefinementHomologyDomainMapExamples (wholeLine)
open TDA.Mapper.RefinementHomologyInterleavingExamples
open scoped NNReal unitInterval

noncomputable section

local instance anyComponentOrder {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (U : ι → Set Y) : LinearOrder (ComponentIndex f U) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-! ## Recovery of the same-space perturbation bound -/

local instance scalePairComponentOrder (c s t : ℝ) :
    LinearOrder (ComponentIndex (scaleMap c) (centredCover s t)) := by
  classical
  apply LinearOrder.lift' (fun a : ComponentIndex (scaleMap c) (centredCover s t) => a.1)
  intro a b hab
  have hsub := scaleMap_zerothHomotopy_subsingleton c s t
  exact Sigma.ext hab (Subsingleton.helim
    (congrArg (fun k => ZerothHomotopy (PullbackSpace (scaleMap c) (centredCover s t) k)) hab)
    a.2 b.2)

/-- The centred Mapper distance bound for the flat and steep unit-interval maps is recovered
from the map-pair theorem with parameter `4`. -/
theorem flatSteep_mapPair_distance_le :
    realInterleavingDistance
      (mapperHomologyPModule ℚ flatMap (centredCover 1) (centredCoverRefinement 1) 0)
      (mapperHomologyPModule ℚ steepMap (centredCover 1) (centredCoverRefinement 1) 0) ≤ 4 := by
  exact realInterleavingDistance_centredMapperPair_le_ofUniformBound ℚ (s := 1) (n := 0)
    flat_steep_dist

/-! ## Different domains with nonisomorphic degree-zero modules -/

private theorem edgePathConnected : PathConnectedSpace (Realization edgeGraph) :=
  edgeHomeomorph.symm.surjective.pathConnectedSpace edgeHomeomorph.symm.continuous

private theorem pointRealization_eq (x : Realization pointGraph) :
    x = vertex pointGraph () := Subsingleton.elim _ _

private def edgeHeight : C(Realization edgeGraph, ℝ) := plHeight edgeGraph tilted

private def edgeCoordReal : C(Realization edgeGraph, ℝ) :=
  ⟨fun x => (edgeHomeomorph x : ℝ), continuous_subtype_val.comp edgeHomeomorph.continuous⟩

private theorem edgeHeight_eq_edgeCoordReal : edgeHeight = edgeCoordReal := by
  apply (plHeight_unique edgeGraph tilted edgeCoordReal (by
    intro b
    cases b <;> simp [edgeCoordReal, tilted,
      edgeHomeomorph_vertex_false, edgeHomeomorph_vertex_true]) (by
    intro d t
    rcases edgeGraph_dart d with hd | hd
    · subst d
      change (edgeHomeomorph (edgePoint edgeGraph d₀ t) : ℝ) =
        GraphPL.dartHeight tilted d₀ t
      rw [edgeHomeomorph_edgePoint]
      simp [GraphPL.dartHeight, tilted, d₀]
    · subst d
      change (edgeHomeomorph (edgePoint edgeGraph d₀.symm t) : ℝ) =
        GraphPL.dartHeight tilted d₀.symm t
      rw [edgeHomeomorph_edgePoint_symm]
      simp [GraphPL.dartHeight, tilted, d₀, unitInterval.coe_symm_eq])).symm

private def pointHeight : C(Realization pointGraph, ℝ) :=
  plHeight pointGraph (fun _ => (1 / 2 : ℝ))

private def edgeToPoint : C(Realization edgeGraph, Realization pointGraph) :=
  ContinuousMap.const _ (vertex pointGraph ())

private def pointToEdge : C(Realization pointGraph, Realization edgeGraph) :=
  ContinuousMap.const _ (edgePoint edgeGraph d₀ half)

private theorem edgeHeight_mem_Icc (x : Realization edgeGraph) :
    edgeHeight x ∈ Set.Icc (0 : ℝ) 1 :=
  plHeight_mem_Icc_of_forall (m := 0) (M := 1)
    (fun b => by cases b <;> norm_num [tilted]) x

private theorem edgeMidpoint_height : edgeHeight (edgePoint edgeGraph d₀ half) = 1 / 2 := by
  simp [edgeHeight, GraphPL.plHeight_edgePoint, GraphPL.dartHeight, tilted, d₀, half]

private theorem pointHeight_apply (x : Realization pointGraph) : pointHeight x = 1 / 2 := by
  rw [pointRealization_eq x]
  simp [pointHeight]

private def pointPath (x y : Realization pointGraph) : Path x y := by
  have hxy : x = y := Subsingleton.elim _ _
  exact hxy ▸ Path.refl x

private def edgePointPair : HeightMapPair edgeHeight pointHeight (1 / 2 : ℝ≥0) where
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
    let γ := pointPath (vertex pointGraph ())
      (edgeToPoint (pointToEdge (vertex pointGraph ())))
    refine ⟨γ, ?_⟩
    intro t
    rw [pointHeight_apply (γ t), pointHeight_apply (vertex pointGraph ())]
    norm_num

private theorem pointMapper_has_no_vertices :
    IsEmpty (ComponentIndex pointHeight (centredCover 1 (1 / 2))) := by
  refine ⟨fun a => ?_⟩
  rcases a with ⟨k, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x =>
    have hm : |(1 / 2 : ℝ) - (k : ℝ)| < 1 / 2 := by
      simpa [pointHeight, pointRealization_eq, centredCover,
        GraphPL.plHeight_vertex] using (mem_centredCover_iff.mp x.2)
    rw [abs_lt] at hm
    have hpos : (0 : ℝ) < (k : ℝ) := by linarith [hm.2]
    have hlt : (k : ℝ) < 1 := by linarith [hm.1]
    have hkpos : 0 < k := by exact_mod_cast hpos
    have hklt : k < 1 := by exact_mod_cast hlt
    omega

private theorem pointMapper_finrank_zero :
    Module.finrank ℚ (simplicialHomology
      (mapper pointHeight (centredCover 1 (1 / 2))) ℚ 0) = 0 := by
  letI : IsEmpty (ComponentIndex pointHeight (centredCover 1 (1 / 2))) :=
    pointMapper_has_no_vertices
  rw [mapper_eq_bot_of_isEmpty_componentIndex pointHeight (centredCover 1 (1 / 2))]
  haveI : Subsingleton (simplicialHomology
      (⊥ : PreAbstractSimplicialComplex
        (ComponentIndex pointHeight (centredCover 1 (1 / 2)))) ℚ 0) :=
    ModuleCat.subsingleton_of_isZero (TDA.Persistence.isZero_simplicialHomology_bot ℚ 0)
  exact Module.finrank_zero_of_subsingleton (R := ℚ)

private theorem scaleMap_one_centred_half_finrank :
    Module.finrank ℚ (simplicialHomology (mapper (scaleMap 1)
      (centredCover 1 (1 / 2))) ℚ 0) = 2 := by
  have hlabels : ∀ k : ℤ, k ∈ ({0, 1} : Finset ℤ) ↔
      ∃ x : unitInterval, scaleMap 1 x ∈ centredCover 1 (1 / 2) k := by
    intro k
    rw [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num [scaleMap, centredCover, Set.mem_Ioo]⟩
      · exact ⟨1, by norm_num [scaleMap, centredCover, Set.mem_Ioo]⟩
    · rintro ⟨x, hx⟩
      rw [mem_centredCover_iff] at hx
      have hx' : |(x : ℝ) - (k : ℝ)| < 1 / 2 := by simpa [scaleMap] using hx
      rw [abs_lt] at hx'
      have hlo : (-1 : ℝ) < (k : ℝ) := by
        have hx0 := x.2.1
        linarith [hx'.2]
      have hhi : (k : ℝ) < 2 := by
        have hx1 := x.2.2
        linarith [hx'.1]
      have hlo' : -1 < k := by exact_mod_cast hlo
      have hhi' : k < 2 := by exact_mod_cast hhi
      omega
  calc
    Module.finrank ℚ (simplicialHomology (mapper (scaleMap 1)
        (centredCover 1 (1 / 2))) ℚ 0) = ({0, 1} : Finset ℤ).card :=
      finrank_scaleMap_centredCover_half 1 {0, 1} hlabels
    _ = 2 := by norm_num

/-- The edge-to-point pair bounds centred Mapper distance by `1/2` in every degree, while the
degree-zero modules are not isomorphic at radius `1/2`. -/
theorem edgeToPoint_mapper_pair (n : ℕ) :
    realInterleavingDistance
      (mapperHomologyPModule ℚ edgeHeight (centredCover 1) (centredCoverRefinement 1) n)
      (mapperHomologyPModule ℚ pointHeight (centredCover 1)
        (centredCoverRefinement 1) n) ≤ 1 / 2 := by
  have h := realInterleavingDistance_centredMapperPair_graphPL_le ℚ 1 n edgePointPair
  norm_num at h ⊢
  exact h

/-- The edge at heights `(0, 1)` and the point at height `1/2` have nonisomorphic degree-zero
centred Mapper modules over `ℚ`. -/
theorem edgeToPoint_mapper_noniso :
    IsEmpty (mapperHomologyPModule ℚ edgeHeight (centredCover 1)
        (centredCoverRefinement 1) 0 ≅
      mapperHomologyPModule ℚ pointHeight (centredCover 1)
        (centredCoverRefinement 1) 0) := by
  refine ⟨fun e => ?_⟩
  have hscale : Module.finrank ℚ (simplicialHomology
      (mapper (scaleMap 1) (centredCover 1 (1 / 2))) ℚ 0) = 2 :=
    scaleMap_one_centred_half_finrank
  have hmap : ∀ x, scaleMap 1 (edgeHomeomorph x) = edgeHeight x := by
    intro x
    rw [edgeHeight_eq_edgeCoordReal]
    simp [scaleMap, edgeCoordReal]
  let iso := mapperHomologyPModuleIso (R := ℚ) (e := edgeHomeomorph) (he := hmap)
    (centredCover 1) (centredCoverRefinement 1) 0
  have hrank := (iso.app (1 / 2)).toLinearEquiv.finrank_eq
  have hrank' : Module.finrank ℚ ((mapperHomologyPModule ℚ edgeHeight
      (centredCover 1) (centredCoverRefinement 1) 0).obj (1 / 2)) =
      Module.finrank ℚ ((mapperHomologyPModule ℚ (scaleMap 1) (centredCover 1)
        (centredCoverRefinement 1) 0).obj (1 / 2)) := by
    simpa only [mapperHomologyPModule_obj] using hrank
  have hscale' : Module.finrank ℚ ((mapperHomologyPModule ℚ (scaleMap 1)
      (centredCover 1) (centredCoverRefinement 1) 0).obj (1 / 2)) = 2 := by
    change Module.finrank ℚ (simplicialHomology
      (mapper (scaleMap 1) (centredCover 1 (1 / 2))) ℚ 0) = 2
    exact hscale
  have hsrc := hrank'.trans hscale'
  have htgt : Module.finrank ℚ ((mapperHomologyPModule ℚ pointHeight
      (centredCover 1) (centredCoverRefinement 1) 0).obj (1 / 2)) = 0 := by
    change Module.finrank ℚ (simplicialHomology
      (mapper pointHeight (centredCover 1 (1 / 2))) ℚ 0) = 0
    exact pointMapper_finrank_zero
  have heq := (e.app (1 / 2)).toLinearEquiv.finrank_eq
  have heq' : Module.finrank ℚ ((mapperHomologyPModule ℚ edgeHeight
      (centredCover 1) (centredCoverRefinement 1) 0).obj (1 / 2)) =
      Module.finrank ℚ ((mapperHomologyPModule ℚ pointHeight
        (centredCover 1) (centredCoverRefinement 1) 0).obj (1 / 2)) := by
    simpa only [mapperHomologyPModule_obj] using heq
  rw [hsrc, htgt] at heq'
  norm_num at heq'

/-! ## Negative control: the path condition -/

private def boolZeroHeight : C(Bool, ℝ) := ContinuousMap.const Bool 0

private def unitZeroHeight : C(Unit, ℝ) := ContinuousMap.const Unit 0

private def boolToUnit : C(Bool, Unit) := ContinuousMap.const Bool ()

private def unitToBool : C(Unit, Bool) := ContinuousMap.const Unit false

private def fullCoverTower (_ : ℝ) : Unit → Set ℝ := wholeLine

private def fullCoverRefinement {s t : ℝ} (_ : s ≤ t) :
    Refinement (fullCoverTower s) (fullCoverTower t) := Refinement.id wholeLine

local instance boolZeroWholeLineOrder :
    LinearOrder (ComponentIndex boolZeroHeight wholeLine) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

local instance boolZeroTowerOrders :
    ∀ t : ℝ, LinearOrder (ComponentIndex boolZeroHeight (fullCoverTower t)) :=
  fun _ => boolZeroWholeLineOrder

private theorem boolZeroMapper_finrank :
    Module.finrank ℚ (simplicialHomology (mapper boolZeroHeight wholeLine) ℚ 0) = 2 := by
  let q : Bool → ZerothHomotopy (PullbackSpace boolZeroHeight wholeLine ()) :=
    fun b => ZerothHomotopy.mk ⟨b, trivial⟩
  have hinj : Function.Injective q := by
    intro a b hab
    by_contra hne
    obtain ⟨p⟩ := Quotient.exact hab
    have hc : Continuous fun t => (p t).1 := continuous_subtype_val.comp p.continuous
    have hconst := PreconnectedSpace.constant inferInstance hc (x := 0) (y := 1)
    simp at hconst
    exact hne hconst
  have hsurj : Function.Surjective q := by
    intro c
    induction c using ZerothHomotopy.rec with
    | mk x => exact ⟨x.1, rfl⟩
  have hcard : Nat.card (ZerothHomotopy
      (PullbackSpace boolZeroHeight wholeLine ())) = 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective q ⟨hinj, hsurj⟩)]
    simp
  have hfinite : Finite (ZerothHomotopy
      (PullbackSpace boolZeroHeight wholeLine ())) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hnoEdges : IsEmpty (Face (mapper boolZeroHeight wholeLine) 1) := by
    refine ⟨fun s => ?_⟩
    have hmult : CoverMultiplicityAtMost boolZeroHeight wholeLine 1 :=
      fun _ _ t _ => by simpa using Finset.card_le_univ t
    have := mapper_face_card_le_of_multiplicity boolZeroHeight wholeLine hmult s.2.1
    omega
  have hfaceEquiv : Face (mapper boolZeroHeight wholeLine) 0 ≃
      ComponentIndex boolZeroHeight wholeLine := by
    refine {
      toFun s := (Finset.card_eq_one.1 s.2.2).choose
      invFun a := ⟨{a}, componentIndex_supported boolZeroHeight wholeLine a,
        Finset.card_singleton a⟩
      left_inv s := Subtype.ext (Finset.card_eq_one.1 s.2.2).choose_spec.symm
      right_inv a := ?_ }
    have h := (Finset.card_eq_one.1 (Finset.card_singleton a)).choose_spec
    exact (Finset.singleton_inj.1 h).symm
  have hcomponents : Nat.card (ComponentIndex boolZeroHeight wholeLine) = 2 := by
    change Nat.card (Σ i : Unit,
      ZerothHomotopy (PullbackSpace boolZeroHeight wholeLine i)) = 2
    calc
      Nat.card (Σ i : Unit, ZerothHomotopy (PullbackSpace boolZeroHeight wholeLine i)) =
          Nat.card (ZerothHomotopy (PullbackSpace boolZeroHeight wholeLine ())) :=
        Nat.card_congr (Equiv.uniqueSigma _)
      _ = 2 := hcard
  have hfiniteComponents : Finite (ComponentIndex boolZeroHeight wholeLine) :=
    Nat.finite_of_card_ne_zero (by rw [hcomponents]; omega)
  letI : Finite (ComponentIndex boolZeroHeight wholeLine) := hfiniteComponents
  have hfiniteFaces : Finite (Face (mapper boolZeroHeight wholeLine) 0) :=
    Finite.of_equiv _ hfaceEquiv.symm
  letI := Fintype.ofFinite (Face (mapper boolZeroHeight wholeLine) 0)
  calc
    Module.finrank ℚ (simplicialHomology (mapper boolZeroHeight wholeLine) ℚ 0) =
        Fintype.card (Face (mapper boolZeroHeight wholeLine) 0) :=
      finrank_zeroHomology_of_no_edges (mapper boolZeroHeight wholeLine) ℚ
    _ = Nat.card (Face (mapper boolZeroHeight wholeLine) 0) := Fintype.card_eq_nat_card
    _ = Nat.card (ComponentIndex boolZeroHeight wholeLine) := Nat.card_congr hfaceEquiv
    _ = 2 := hcomponents

private theorem unitZeroMapper_finrank :
    Module.finrank ℚ (simplicialHomology (mapper unitZeroHeight wholeLine) ℚ 0) = 1 :=
  finrank_simplicialHomology_mapper_full_zero unitZeroHeight ℚ

/-- Constant, height-preserving maps from discrete `Bool` to `Unit` do not form a height-map
pair at parameter `0`: the reverse composite would require a path from `true` to `false`.
Their Mapper modules for the constant full-cover tower have distance `⊤` in degree zero. -/
theorem boolToUnit_pathCondition_needed :
    (∀ b, unitZeroHeight (boolToUnit b) = boolZeroHeight b) ∧
      (∀ u, boolZeroHeight (unitToBool u) = unitZeroHeight u) ∧
      ¬ Nonempty (HeightMapPair boolZeroHeight unitZeroHeight 0) ∧
      realInterleavingDistance
        (mapperHomologyPModule ℚ boolZeroHeight fullCoverTower fullCoverRefinement 0)
        (mapperHomologyPModule ℚ unitZeroHeight fullCoverTower fullCoverRefinement 0) = ⊤ := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · rintro ⟨P⟩
    have htrue : P.ψ (P.φ true) = true := by
      obtain ⟨γ, _⟩ := P.hψφ true
      have hconst := PreconnectedSpace.constant inferInstance γ.continuous (x := 0) (y := 1)
      simpa using hconst
    have hfalse : P.ψ (P.φ false) = false := by
      obtain ⟨γ, _⟩ := P.hψφ false
      have hconst := PreconnectedSpace.constant inferInstance γ.continuous (x := 0) (y := 1)
      simpa using hconst
    have hcomp : P.ψ (P.φ true) = P.ψ (P.φ false) :=
      congrArg P.ψ (Subsingleton.elim (P.φ true) (P.φ false))
    exact Bool.false_ne_true (htrue.symm.trans (hcomp.trans hfalse)).symm
  · apply le_antisymm le_top
    apply le_realInterleavingDistance_of_finrank_lt
      (k := ℚ)
      (M := mapperHomologyPModule ℚ boolZeroHeight fullCoverTower fullCoverRefinement 0)
      (N := mapperHomologyPModule ℚ unitZeroHeight fullCoverTower fullCoverRefinement 0)
      (r := ⊤)
    intro ε hε
    have h : (1 : ℝ) ≤ 1 + ((ε + ε : ℝ≥0) : ℝ) := by
      linarith [NNReal.coe_nonneg (ε + ε)]
    have hmapBij : Function.Bijective
        (mapperHomologyMap ℚ boolZeroHeight (fullCoverRefinement h) 0).hom := by
      change Function.Bijective
        (mapperHomologyMap ℚ boolZeroHeight (Refinement.id wholeLine) 0).hom
      rw [mapperHomologyMap_id]
      constructor
      · intro x y hxy
        exact hxy
      · intro y
        exact ⟨y, rfl⟩
    have hsurj : Function.Surjective (structureMapLinear
        (mapperHomologyPModule ℚ boolZeroHeight fullCoverTower fullCoverRefinement 0) h) := by
      change Function.Surjective
        ((mapperHomologyMap ℚ boolZeroHeight (fullCoverRefinement h) 0).hom)
      exact hmapBij.2
    have hrank : Module.finrank ℚ (LinearMap.range (structureMapLinear
        (mapperHomologyPModule ℚ boolZeroHeight fullCoverTower fullCoverRefinement 0) h)) = 2 := by
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top]
      change Module.finrank ℚ (simplicialHomology (mapper boolZeroHeight wholeLine) ℚ 0) = 2
      exact boolZeroMapper_finrank
    have htarget : Module.finrank ℚ ((mapperHomologyPModule ℚ unitZeroHeight
        fullCoverTower fullCoverRefinement 0).obj (1 + ε)) = 1 := by
      change Module.finrank ℚ (simplicialHomology (mapper unitZeroHeight wholeLine) ℚ 0) = 1
      exact unitZeroMapper_finrank
    refine ⟨1, h, Module.finite_of_finrank_eq_succ htarget, ?_⟩
    rw [htarget, hrank]
    norm_num

end

end TDA.Mapper.RefinementHomologyMapPairExamples
