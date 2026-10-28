import TDA.Mapper.RefinementHomologyMapPair
import TDA.Mapper.RefinementHomologyInterleavingExamples
import TDA.Mapper.RefinementHomologyLowerBound
import TDA.Mapper.RefinementHomologyLowerBoundExamples
import TDA.Mapper.RefinementHomologyDomainMapExamples
import TDA.Mapper.RefinementHomologyEssential
import TDA.Mapper.GraphPLReebMapPairExamples
import TDA.Reeb.GraphRealizationExamples
import TDA.Reeb.GraphPLVertexPerturbationExamples
import TDA.Simplicial.H0Augmentation

/-!
# Fixtures for centred Mapper homology map-pair bounds

The fixed-space perturbation bound is recovered by the map-pair theorem. On the single edge of
heights `0` and `1`, a map pair to a point at height `1/2` gives distance at most `1/2`, although
the degree-zero modules are not isomorphic at radius `1/2`. The constant height maps from discrete
`Bool` to `Unit` preserve heights but admit no `HeightMapPair` at any parameter. For their
degree-zero Mapper modules over `ℚ`, this file proves the lower bound `1/2` on the centred tower
of spacing `1` (the value itself is not determined here) and the exact value `⊤` on the constant
full-cover tower.
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
open scoped NNReal ENNReal unitInterval

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

/-- At radius `1/2`, the edge at heights `(0, 1)` and the point at height `1/2` have degree-zero
centred Mapper dimensions `2` and `0`, respectively, over `ℚ`. -/
theorem edgeToPoint_mapper_dimensions :
    Module.finrank ℚ ((mapperHomologyPModule ℚ edgeHeight (centredCover 1)
      (centredCoverRefinement 1) 0).obj (1 / 2)) = 2 ∧
    Module.finrank ℚ ((mapperHomologyPModule ℚ pointHeight (centredCover 1)
      (centredCoverRefinement 1) 0).obj (1 / 2)) = 0 := by
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
  constructor
  · exact hrank'.trans hscale'
  · change Module.finrank ℚ (simplicialHomology
      (mapper pointHeight (centredCover 1 (1 / 2))) ℚ 0) = 0
    exact pointMapper_finrank_zero

/-- The edge at heights `(0, 1)` and the point at height `1/2` have nonisomorphic degree-zero
centred Mapper modules over `ℚ`. -/
theorem edgeToPoint_mapper_noniso :
    IsEmpty (mapperHomologyPModule ℚ edgeHeight (centredCover 1)
        (centredCoverRefinement 1) 0 ≅
      mapperHomologyPModule ℚ pointHeight (centredCover 1)
        (centredCoverRefinement 1) 0) := by
  refine ⟨fun e => ?_⟩
  have hsrc := edgeToPoint_mapper_dimensions.1
  have htgt := edgeToPoint_mapper_dimensions.2
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

private theorem zeroHeight_componentIndex_label_eq_zero {X : Type} [TopologicalSpace X]
    (f : C(X, ℝ)) (hf : ∀ x, f x = 0) {r : ℝ} (hr : r < 1)
    (a : ComponentIndex f (centredCover 1 r)) : a.1 = 0 := by
  obtain ⟨x, _⟩ := ZerothHomotopy.mk_surjective a.2
  have hmem : |(a.1 : ℝ)| < r := by
    have h := mem_centredCover_iff.mp x.2
    simpa [hf x.1] using h
  have hkReal : |(a.1 : ℝ)| < 1 := hmem.trans hr
  have hkInt : |a.1| < 1 := by exact_mod_cast hkReal
  exact Int.abs_lt_one_iff.1 hkInt

private theorem zeroHeight_mapper_no_edges {X : Type} [TopologicalSpace X]
    (f : C(X, ℝ)) (hf : ∀ x, f x = 0) {r : ℝ} (hr : r < 1) :
    IsEmpty (Face (mapper f (centredCover 1 r)) 1) := by
  refine ⟨fun F => ?_⟩
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.1 F.2.2
  have hface := F.2.1
  rw [hF] at hface
  have ha := zeroHeight_componentIndex_label_eq_zero f hf hr a
  have hb := zeroHeight_componentIndex_label_eq_zero f hf hr b
  exact hab (eq_of_mem_mapper_face_of_fst_eq f _ hface (by simp) (by simp)
    (ha.trans hb.symm))

private noncomputable def mapper_vertexFace_equiv {X ι : Type} [TopologicalSpace X]
    (f : C(X, ℝ)) (U : ι → Set ℝ) [LinearOrder (ComponentIndex f U)] :
    Face (mapper f U) 0 ≃ ComponentIndex f U := by
  classical
  refine {
    toFun := fun s => (Finset.card_eq_one.1 s.2.2).choose
    invFun := fun a => ⟨{a}, componentIndex_supported f U a, Finset.card_singleton a⟩
    left_inv := fun s => Subtype.ext (Finset.card_eq_one.1 s.2.2).choose_spec.symm
    right_inv := fun a => ?_ }
  have h := (Finset.card_eq_one.1 (Finset.card_singleton a)).choose_spec
  exact (Finset.singleton_inj.1 h).symm

private noncomputable def boolZeroComponentIndexVertex {r : ℝ} (hr : 0 < r) (b : Bool) :
    ComponentIndex boolZeroHeight (centredCover 1 r) :=
  ⟨0, ZerothHomotopy.mk ⟨b, by
    rw [mem_centredCover_iff]
    simpa [boolZeroHeight] using hr⟩⟩

private noncomputable def boolZeroComponentIndexEquiv {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    Bool ≃ ComponentIndex boolZeroHeight (centredCover 1 r) := by
  classical
  let q := boolZeroComponentIndexVertex hr
  have hq : Function.Bijective q := by
    constructor
    · intro a b hab
      have hclass :
          ZerothHomotopy.mk (⟨a, by
            rw [mem_centredCover_iff]
            simpa [boolZeroHeight] using hr⟩ :
              PullbackSpace boolZeroHeight (centredCover 1 r) 0) =
          ZerothHomotopy.mk (⟨b, by
            rw [mem_centredCover_iff]
            simpa [boolZeroHeight] using hr⟩ :
              PullbackSpace boolZeroHeight (centredCover 1 r) 0) := by
        have hparts := Sigma.ext_iff.mp hab
        exact eq_of_heq hparts.2
      by_contra hne
      obtain ⟨p⟩ := Quotient.exact hclass
      have hc : Continuous fun t => (p t).1 := continuous_subtype_val.comp p.continuous
      have hconst := PreconnectedSpace.constant inferInstance hc (x := 0) (y := 1)
      exact hne (by simpa using hconst)
    · intro a
      rcases a with ⟨k, c⟩
      have hk := zeroHeight_componentIndex_label_eq_zero boolZeroHeight
        (by intro _; rfl) hr' ⟨k, c⟩
      change k = 0 at hk
      subst k
      obtain ⟨x, hx⟩ := ZerothHomotopy.mk_surjective c
      refine ⟨x.1, ?_⟩
      change boolZeroComponentIndexVertex hr x.1 = ⟨0, c⟩
      unfold boolZeroComponentIndexVertex
      exact Sigma.ext rfl (heq_of_eq (calc
        ZerothHomotopy.mk (⟨x.1, by
          rw [mem_centredCover_iff]
          simpa [boolZeroHeight] using hr⟩ :
            PullbackSpace boolZeroHeight (centredCover 1 r) 0) = ZerothHomotopy.mk x := by
              congr 1
        _ = c := hx))
  exact Equiv.ofBijective q hq

private theorem boolZeroMapper_centredMap_bijective {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) :
    Function.Bijective (mapperMap boolZeroHeight (centredCoverRefinement 1 hab)) := by
  let ea := boolZeroComponentIndexEquiv ha (lt_of_le_of_lt hab hb)
  let eb := boolZeroComponentIndexEquiv (lt_of_lt_of_le ha hab) hb
  have hmap (x : Bool) :
      mapperMap boolZeroHeight (centredCoverRefinement 1 hab) (ea x) = eb x := by
    change mapperMap boolZeroHeight (centredCoverRefinement 1 hab)
        (boolZeroComponentIndexVertex ha x) =
          boolZeroComponentIndexVertex (lt_of_lt_of_le ha hab) x
    unfold boolZeroComponentIndexVertex
    rw [mapperMap_mk]
    apply Sigma.ext rfl
    apply heq_of_eq
    apply congrArg ZerothHomotopy.mk
    exact Subtype.ext rfl
  constructor
  · intro x y hxy
    obtain ⟨u, rfl⟩ := ea.surjective x
    obtain ⟨v, rfl⟩ := ea.surjective y
    have huv : u = v := eb.injective ((hmap u).symm.trans (hxy.trans (hmap v)))
    subst v
    rfl
  · intro y
    obtain ⟨v, rfl⟩ := eb.surjective y
    exact ⟨ea v, hmap v⟩

private theorem boolZeroMapper_centred_finrank {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    Module.finrank ℚ (simplicialHomology
      (mapper boolZeroHeight (centredCover 1 r)) ℚ 0) = 2 := by
  let e := boolZeroComponentIndexEquiv hr hr'
  letI : Fintype (ComponentIndex boolZeroHeight (centredCover 1 r)) :=
    Fintype.ofEquiv Bool e
  let hfaceEquiv := mapper_vertexFace_equiv boolZeroHeight (centredCover 1 r)
  letI : Fintype (Face (mapper boolZeroHeight (centredCover 1 r)) 0) :=
    Fintype.ofEquiv (ComponentIndex boolZeroHeight (centredCover 1 r)) hfaceEquiv.symm
  letI : IsEmpty (Face (mapper boolZeroHeight (centredCover 1 r)) 1) :=
    zeroHeight_mapper_no_edges boolZeroHeight (by intro _; rfl) hr'
  calc
    Module.finrank ℚ (simplicialHomology
        (mapper boolZeroHeight (centredCover 1 r)) ℚ 0) =
        Fintype.card (Face (mapper boolZeroHeight (centredCover 1 r)) 0) :=
      finrank_zeroHomology_of_no_edges (mapper boolZeroHeight (centredCover 1 r)) ℚ
    _ = Fintype.card (ComponentIndex boolZeroHeight (centredCover 1 r)) :=
      Fintype.card_congr hfaceEquiv
    _ = 2 := by
      rw [← Fintype.card_congr e]
      simp

private theorem unitZeroMapper_centred_half_finrank :
    Module.finrank ℚ (simplicialHomology
      (mapper unitZeroHeight (centredCover 1 (1 / 2))) ℚ 0) = 1 := by
  letI : Unique (ComponentIndex unitZeroHeight (centredCover 1 (1 / 2))) := by
    refine ⟨⟨0, ZerothHomotopy.mk ⟨(), by
      rw [mem_centredCover_iff]
      norm_num [unitZeroHeight]⟩⟩, ?_⟩
    intro a
    rcases a with ⟨k, c⟩
    have hk := zeroHeight_componentIndex_label_eq_zero unitZeroHeight
      (by intro _; rfl) (by norm_num) ⟨k, c⟩
    change k = 0 at hk
    subst k
    obtain ⟨x, hx⟩ := ZerothHomotopy.mk_surjective c
    change (⟨0, c⟩ : ComponentIndex unitZeroHeight (centredCover 1 (1 / 2))) =
      ⟨0, ZerothHomotopy.mk (⟨(), by
        rw [mem_centredCover_iff]
        norm_num [unitZeroHeight]⟩ :
          PullbackSpace unitZeroHeight (centredCover 1 (1 / 2)) 0)⟩
    exact Sigma.ext rfl (heq_of_eq (calc
      c = ZerothHomotopy.mk x := hx.symm
      _ = ZerothHomotopy.mk (⟨(), by
        rw [mem_centredCover_iff]
        norm_num [unitZeroHeight]⟩ :
          PullbackSpace unitZeroHeight (centredCover 1 (1 / 2)) 0) := by
            congr 1))
  letI : Fintype (ComponentIndex unitZeroHeight (centredCover 1 (1 / 2))) :=
    Fintype.ofFinite _
  let hfaceEquiv := mapper_vertexFace_equiv unitZeroHeight (centredCover 1 (1 / 2))
  letI : Fintype (Face (mapper unitZeroHeight (centredCover 1 (1 / 2))) 0) :=
    Fintype.ofEquiv (ComponentIndex unitZeroHeight (centredCover 1 (1 / 2))) hfaceEquiv.symm
  letI : IsEmpty (Face (mapper unitZeroHeight (centredCover 1 (1 / 2))) 1) :=
    zeroHeight_mapper_no_edges unitZeroHeight (by intro _; rfl) (by norm_num)
  calc
    Module.finrank ℚ (simplicialHomology
        (mapper unitZeroHeight (centredCover 1 (1 / 2))) ℚ 0) =
        Fintype.card (Face (mapper unitZeroHeight (centredCover 1 (1 / 2))) 0) :=
      finrank_zeroHomology_of_no_edges (mapper unitZeroHeight (centredCover 1 (1 / 2))) ℚ
    _ = Fintype.card (ComponentIndex unitZeroHeight (centredCover 1 (1 / 2))) :=
      Fintype.card_congr hfaceEquiv
    _ = 1 := by
      simp

private theorem boolToUnit_centred_distance_ge_half :
    ENNReal.ofReal (1 / 2) ≤ realInterleavingDistance
      (mapperHomologyPModule ℚ boolZeroHeight (centredCover 1)
        (centredCoverRefinement 1) 0)
      (mapperHomologyPModule ℚ unitZeroHeight (centredCover 1)
        (centredCoverRefinement 1) 0) := by
  have hbound : ((1 / 2 : ℝ≥0) : ℝ≥0∞) ≤ realInterleavingDistance
      (mapperHomologyPModule ℚ boolZeroHeight (centredCover 1)
        (centredCoverRefinement 1) 0)
      (mapperHomologyPModule ℚ unitZeroHeight (centredCover 1)
        (centredCoverRefinement 1) 0) := by
    apply le_realInterleavingDistance_of_finrank_lt (k := ℚ)
      (M := mapperHomologyPModule ℚ boolZeroHeight (centredCover 1)
        (centredCoverRefinement 1) 0)
      (N := mapperHomologyPModule ℚ unitZeroHeight (centredCover 1)
        (centredCoverRefinement 1) 0)
      (r := (1 / 2 : ℝ≥0))
    intro ε hε
    have hε' : (ε : ℝ≥0∞) < ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by simpa using hε
    have hεReal : (ε : ℝ) < 1 / 2 := by
      exact_mod_cast ENNReal.coe_lt_coe.1 hε'
    let t : ℝ := (1 - 2 * (ε : ℝ)) / 2
    have htpos : 0 < t := by dsimp [t]; linarith
    have hmid : t + (ε : ℝ) = 1 / 2 := by dsimp [t]; ring
    have hdouble : t + ((ε + ε : ℝ≥0) : ℝ) = 1 / 2 + (ε : ℝ) := by
      dsimp [t]
      ring
    have hdouble_pos : 0 < t + ((ε + ε : ℝ≥0) : ℝ) := by rw [hdouble]; positivity
    have hdouble_lt : t + ((ε + ε : ℝ≥0) : ℝ) < 1 := by
      rw [hdouble]
      linarith
    have h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ) := by
      rw [hdouble]
      linarith [ε.coe_nonneg]
    have hmapBij : Function.Bijective (mapperMap boolZeroHeight
        (centredCoverRefinement 1 h)) :=
      boolZeroMapper_centredMap_bijective htpos h hdouble_lt
    letI : IsEmpty (Face (mapper boolZeroHeight
        (centredCover 1 (t + ((ε + ε : ℝ≥0) : ℝ)))) 1) :=
      zeroHeight_mapper_no_edges boolZeroHeight (by intro _; rfl) hdouble_lt
    have hhomBij : Function.Bijective
        (mapperHomologyMap ℚ boolZeroHeight (centredCoverRefinement 1 h) 0).hom :=
      RefinementHomologyLowerBoundExamples.mapperHomologyMap_bijective_of_bijective
        ℚ boolZeroHeight _ hmapBij 0
    have hsurj : Function.Surjective (structureMapLinear
        (mapperHomologyPModule ℚ boolZeroHeight (centredCover 1)
          (centredCoverRefinement 1) 0) h) := by
      change Function.Surjective
        (mapperHomologyMap ℚ boolZeroHeight (centredCoverRefinement 1 h) 0).hom
      exact hhomBij.2
    have hrank : Module.finrank ℚ (LinearMap.range (structureMapLinear
        (mapperHomologyPModule ℚ boolZeroHeight (centredCover 1)
          (centredCoverRefinement 1) 0) h)) = 2 := by
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top]
      change Module.finrank ℚ (simplicialHomology
        (mapper boolZeroHeight (centredCover 1 (t + ((ε + ε : ℝ≥0) : ℝ)))) ℚ 0) = 2
      exact boolZeroMapper_centred_finrank hdouble_pos hdouble_lt
    have htarget : Module.finrank ℚ ((mapperHomologyPModule ℚ unitZeroHeight
        (centredCover 1) (centredCoverRefinement 1) 0).obj (t + (ε : ℝ))) = 1 := by
      change Module.finrank ℚ (simplicialHomology
        (mapper unitZeroHeight (centredCover 1 (t + (ε : ℝ)))) ℚ 0) = 1
      rw [hmid]
      exact unitZeroMapper_centred_half_finrank
    refine ⟨t, h, Module.finite_of_finrank_eq_succ htarget, ?_⟩
    rw [htarget, hrank]
    norm_num
  have hconvert : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    have hreal : (1 / 2 : ℝ) = ((1 / 2 : ℝ≥0) : ℝ) := by norm_num
    rw [hreal, ENNReal.ofReal_coe_nnreal]
    norm_num
  simpa [hconvert] using hbound

/-- The constant maps from discrete `Bool` to `Unit` preserve heights but admit no height-map pair
at any parameter, since the reverse composite would require a path from `true` to `false`. For
their degree-zero Mapper modules over `ℚ`, the fourth conjunct is the lower bound `1/2` on the
centred tower of spacing `1` (only this bound is proved here) and the fifth is the exact value
`⊤` on the constant full-cover tower. -/
theorem boolToUnit_pathCondition_needed :
    (∀ b, unitZeroHeight (boolToUnit b) = boolZeroHeight b) ∧
      (∀ u, boolZeroHeight (unitToBool u) = unitZeroHeight u) ∧
      (∀ δ : ℝ≥0, ¬ Nonempty (HeightMapPair boolZeroHeight unitZeroHeight δ)) ∧
      ENNReal.ofReal (1 / 2) ≤ realInterleavingDistance
        (mapperHomologyPModule ℚ boolZeroHeight (centredCover 1)
          (centredCoverRefinement 1) 0)
        (mapperHomologyPModule ℚ unitZeroHeight (centredCover 1)
          (centredCoverRefinement 1) 0) ∧
      realInterleavingDistance
        (mapperHomologyPModule ℚ boolZeroHeight fullCoverTower fullCoverRefinement 0)
        (mapperHomologyPModule ℚ unitZeroHeight fullCoverTower fullCoverRefinement 0) = ⊤ := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, boolToUnit_centred_distance_ge_half, ?_⟩
  · intro δ
    rintro ⟨P⟩
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
