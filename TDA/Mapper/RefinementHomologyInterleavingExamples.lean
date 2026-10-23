import TDA.Mapper.RefinementHomologyInterleaving
import TDA.Mapper.RefinementHomologyExamples
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.UnitInterval

/-!
# Interleaving fixtures for Mapper homology modules

A tower interleaved with itself at `η = 0` gives the identity isomorphism of its Mapper
homology module. Over a one-point domain, cover maps whose composite selector is not the
tower selector still give an interleaving. The centred tower, whose members are empty at
nonpositive radius, is interleaved with its own shift. Over the unit interval, the constant
map `0` and the map `x ↦ 4x` have Mapper homology modules along the centred tower of spacing
`1` at distance at most `4`, while their `H₀` over `ℚ` at radius `1/2` has dimensions `1` and
`5`, so the two modules are not isomorphic. For the identity map, the pulled-back tower is the
original tower. The control pairs equal homology maps of refinements with the different
homology maps of two simplicial maps that are not induced by refinements.
-/

namespace TDA.Mapper.RefinementHomologyInterleavingExamples

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence
open TDA.Mapper.TowerExamples
open TDA.Mapper.RefinementHomologyExamples
open scoped NNReal unitInterval

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w c

/-! ## Zero shift and identical towers -/

/-- Interleaving a tower with itself at `η = 0`, with tower refinements as cover maps, gives
the identity isomorphism of its Mapper homology module. -/
theorem mapperHomologyInterleaving_zero_toIso {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (R : Type c) [Ring R] (f : C(X, Y)) {Index : ℝ → Type w}
    {U : (t : ℝ) → Index t → Set Y} [∀ t, LinearOrder (ComponentIndex f (U t))]
    (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t)) (n : ℕ) :
    (mapperHomologyInterleaving R f rU rU (η := 0)
        (fun t => rU (by simp)) (fun t => rU (by simp)) n).toIso = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext t
  exact (mapperHomologyMap_comp_eq R f _ _ (Refinement.id (U t)) n).trans
    (mapperHomologyMap_id R f n)

/-! ## Cover maps without coherence over a one-point domain -/

local instance {ι : Type} [LinearOrder ι] (U : ι → Set Unit) :
    LinearOrder (ComponentIndex threeStageMap U) :=
  componentIndexLinearOrder threeStageMap U

/-- A tower of two duplicated copies of the one-point space. -/
def duplicatedTower (_ : ℝ) : Bool → Set Unit := fun _ => Set.univ

/-- The identity-selector tower refinement. -/
def duplicatedRefinement {s t : ℝ} (_ : s ≤ t) :
    Refinement (duplicatedTower s) (duplicatedTower t) where
  selector b := b
  subset _ := subset_rfl

/-- A cover map selecting the first copy. -/
def selectFirst (s t : ℝ) : Refinement (duplicatedTower s) (duplicatedTower t) where
  selector _ := false
  subset _ := subset_rfl

/-- Cover maps selecting the first copy and identity cover maps compose to a selector that
differs from the tower selector, and they still interleave the Mapper homology module of the
duplicated tower with itself. -/
theorem duplicatedTower_interleaving (η : ℝ≥0) (n : ℕ) (t : ℝ) :
    (Refinement.comp (selectFirst t (t + η))
        (duplicatedRefinement (s := t + η) (t := t + η + η)
          (le_add_of_nonneg_right (NNReal.coe_nonneg η)))).selector ≠
      (duplicatedRefinement (s := t) (t := t + η + η) (by linarith [NNReal.coe_nonneg η])).selector ∧
    Nonempty (RealInterleaving η
      (mapperHomologyPModule ℚ threeStageMap duplicatedTower duplicatedRefinement n)
      (mapperHomologyPModule ℚ threeStageMap duplicatedTower duplicatedRefinement n)) := by
  refine ⟨fun h => Bool.false_ne_true (congrFun h true), ⟨?_⟩⟩
  exact mapperHomologyInterleaving ℚ threeStageMap duplicatedRefinement duplicatedRefinement
    (fun t => selectFirst t (t + η)) (fun _ => duplicatedRefinement (le_add_of_nonneg_right
      (NNReal.coe_nonneg η))) n

/-! ## An empty start -/

/-- The centred tower is interleaved with its own `η`-shift, and its Mapper complexes have no
faces at nonpositive radius. No inhabitedness assumption is made on the domain. -/
theorem centredCover_shift_interleaving {X : Type u} [TopologicalSpace X] (R : Type c) [Ring R]
    (f : C(X, ℝ)) (s : ℝ) [∀ t, LinearOrder (ComponentIndex f (centredCover s t))]
    (η : ℝ≥0) (n : ℕ) :
    Nonempty (RealInterleaving η
      (mapperHomologyPModule R f (centredCover s) (centredCoverRefinement s) n)
      (mapperHomologyPModule R f (fun t => centredCover s (t + η))
        (fun h => centredCoverRefinement s (add_le_add h le_rfl)) n)) ∧
    ∀ t ≤ 0, ∀ m, IsEmpty (Face (mapper f (centredCover s t)) m) := by
  refine ⟨⟨mapperHomologyInterleaving R f (centredCoverRefinement s)
    (fun h => centredCoverRefinement s (add_le_add h le_rfl))
    (fun t => centredCoverRefinement s (by linarith [NNReal.coe_nonneg η]))
    (fun t => centredCoverRefinement s le_rfl) n⟩, ?_⟩
  intro t ht m
  refine ⟨fun F => ?_⟩
  obtain ⟨⟨a, _⟩, x, hx⟩ := (mem_mapper_iff f (centredCover s t) F.1).1 F.2.1
  obtain ⟨hxa, _⟩ := hx a ‹_›
  rw [centredCover_eq_empty ht] at hxa
  exact hxa

/-! ## Perturbation of a map on the unit interval -/

/-- Multiplication by a constant on the unit interval. -/
def scaleMap (c : ℝ) : C(I, ℝ) :=
  ⟨fun x => c * (x : ℝ), continuous_const.mul continuous_subtype_val⟩

/-- Every pulled-back centred member has at most one path component. -/
theorem scaleMap_zerothHomotopy_subsingleton (c s t : ℝ) (k : ℤ) :
    Subsingleton (ZerothHomotopy (PullbackSpace (scaleMap c) (centredCover s t) k)) := by
  constructor
  intro p q
  induction p using ZerothHomotopy.rec with
  | mk p =>
  induction q using ZerothHomotopy.rec with
  | mk q =>
  let T : Set ℝ := Set.Icc 0 1 ∩ (LinearMap.mulLeft ℝ c) ⁻¹' centredCover s t k
  have hT : Convex ℝ T := (convex_Icc 0 1).inter ((convex_Ioo _ _).linear_preimage _)
  have hp : (p.1 : ℝ) ∈ T := ⟨p.1.2, p.2⟩
  have hq : (q.1 : ℝ) ∈ T := ⟨q.1.2, q.2⟩
  have hj := ((hT.isPathConnected ⟨_, hp⟩).joinedIn _ hp _ hq).map
    (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one))
  rw [Set.projIcc_val, Set.projIcc_val] at hj
  refine mk_eq_of_joinedIn (scaleMap c) (centredCover s t k) (hj.mono ?_) p.2 q.2
  rintro _ ⟨r, hr, rfl⟩
  change c * (Set.projIcc 0 1 zero_le_one r : ℝ) ∈ centredCover s t k
  rw [Set.projIcc_of_mem _ hr.1]
  exact hr.2

/-- Component indices of a scaled map, ordered by their cover labels. -/
local instance scaleMapComponentOrder (c s t : ℝ) :
    LinearOrder (ComponentIndex (scaleMap c) (centredCover s t)) :=
  LinearOrder.lift' (fun a => a.1) (by
    intro a b h
    have := scaleMap_zerothHomotopy_subsingleton c s t
    exact Sigma.ext h (Subsingleton.helim (congrArg (fun k =>
      ZerothHomotopy (PullbackSpace (scaleMap c) (centredCover s t) k)) h) a.2 b.2))

/-- The Mapper complex of a real-valued map along the centred family of spacing `1` and radius
`1/2` has no edges, since its members are pairwise disjoint. -/
theorem centredCover_half_no_edges {X : Type} [TopologicalSpace X] (f : C(X, ℝ))
    [LinearOrder (ComponentIndex f (centredCover 1 (1 / 2)))] :
    IsEmpty (Face (mapper f (centredCover 1 (1 / 2))) 1) := by
  refine ⟨fun F => ?_⟩
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.1 F.2.2
  have hface := F.2.1
  rw [hF] at hface
  obtain ⟨_, x, hx⟩ := (mem_mapper_iff f _ _).1 hface
  obtain ⟨ha, _⟩ := hx a (by simp)
  obtain ⟨hb, _⟩ := hx b (by simp)
  rw [mem_centredCover_iff] at ha hb
  have hlt : |((a.1 : ℝ) - b.1)| < 1 := by
    have := abs_sub_le (a.1 : ℝ) (f x) (b.1)
    rw [abs_sub_comm (a.1 : ℝ) (f x)] at this
    simp only [mul_one] at ha hb
    linarith
  have hkey : a.1 = b.1 := by
    rw [abs_lt] at hlt
    have h₁ : a.1 - b.1 < 1 := by exact_mod_cast hlt.2
    have h₂ : -1 < a.1 - b.1 := by exact_mod_cast hlt.1
    omega
  exact hab (eq_of_mem_mapper_face_of_fst_eq f _ hface (by simp) (by simp) hkey)

private def vertexFace {X : Type} [TopologicalSpace X] (f : C(X, ℝ)) (U : ℤ → Set ℝ)
    [LinearOrder (ComponentIndex f U)] (a : ComponentIndex f U) : Face (mapper f U) 0 :=
  ⟨{a}, componentIndex_supported f U a, by simp⟩

private theorem vertexFace_bijective {X : Type} [TopologicalSpace X] (f : C(X, ℝ))
    (U : ℤ → Set ℝ) [LinearOrder (ComponentIndex f U)] :
    Function.Bijective (vertexFace f U) := by
  constructor
  · intro a b h
    exact Finset.singleton_injective (congrArg Subtype.val h)
  · intro F
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 F.2.2
    exact ⟨a, Subtype.ext ha.symm⟩

/-- Over `ℚ`, `H₀` of the Mapper complex of a scaled map along the centred family of spacing `1`
and radius `1/2` has dimension the number of labels whose member meets the image. -/
theorem finrank_scaleMap_centredCover_half (c : ℝ) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ ∃ x : I, c * (x : ℝ) ∈ centredCover 1 (1 / 2) k) :
    Module.finrank ℚ
        (simplicialHomology (mapper (scaleMap c) (centredCover 1 (1 / 2))) ℚ 0) = S.card := by
  have hbij : Function.Bijective (fun a : ComponentIndex (scaleMap c) (centredCover 1 (1 / 2)) =>
      (⟨a.1, (hS a.1).2 (by
        induction a.2 using ZerothHomotopy.rec with
        | mk x => exact ⟨x.1, x.2⟩)⟩ : S)) := by
    constructor
    · intro a b h
      have := scaleMap_zerothHomotopy_subsingleton c 1 (1 / 2)
      have h' : a.1 = b.1 := congrArg Subtype.val h
      exact Sigma.ext h' (Subsingleton.helim (congrArg (fun k =>
        ZerothHomotopy (PullbackSpace (scaleMap c) (centredCover 1 (1 / 2)) k)) h') a.2 b.2)
    · rintro ⟨k, hk⟩
      obtain ⟨x, hx⟩ := (hS k).1 hk
      exact ⟨⟨k, ZerothHomotopy.mk ⟨x, hx⟩⟩, rfl⟩
  let e : Face (mapper (scaleMap c) (centredCover 1 (1 / 2))) 0 ≃ S :=
    (Equiv.ofBijective _ (vertexFace_bijective _ _)).symm.trans (Equiv.ofBijective _ hbij)
  have := centredCover_half_no_edges (scaleMap c)
  let _ : Fintype (Face (mapper (scaleMap c) (centredCover 1 (1 / 2))) 0) := Fintype.ofEquiv S e.symm
  rw [finrank_zeroHomology_of_no_edges, Fintype.card_congr e, Fintype.card_coe]

private theorem mem_centredCover_half_iff (y : ℝ) (k : ℤ) :
    y ∈ centredCover 1 (1 / 2) k ↔ (k : ℝ) - 1 / 2 < y ∧ y < k + 1 / 2 := by
  simp [centredCover]

/-- The constant map `0` on the unit interval. -/
abbrev flatMap : C(I, ℝ) := scaleMap 0

/-- The map `x ↦ 4x` on the unit interval. -/
abbrev steepMap : C(I, ℝ) := scaleMap 4

/-- The flat and steep maps are at pointwise distance at most `4`. -/
theorem flat_steep_dist (x : I) : |flatMap x - steepMap x| ≤ ((4 : ℝ≥0) : ℝ) := by
  change |0 * (x : ℝ) - 4 * x| ≤ 4
  rw [zero_mul, zero_sub, abs_neg, abs_of_nonneg (by linarith [x.2.1])]
  linarith [x.2.2]

/-- Along the centred tower of spacing `1`, the flat map has one-dimensional `H₀` over `ℚ` at
radius `1/2`, the steep map has five-dimensional `H₀` there, the two Mapper homology modules
are not isomorphic, and their real interleaving distance is at most `4`. -/
theorem flat_steep_perturbation :
    Module.finrank ℚ ((mapperHomologyPModule ℚ flatMap (centredCover 1)
        (centredCoverRefinement 1) 0).obj (1 / 2)) = 1 ∧
    Module.finrank ℚ ((mapperHomologyPModule ℚ steepMap (centredCover 1)
        (centredCoverRefinement 1) 0).obj (1 / 2)) = 5 ∧
    IsEmpty (mapperHomologyPModule ℚ flatMap (centredCover 1) (centredCoverRefinement 1) 0 ≅
      mapperHomologyPModule ℚ steepMap (centredCover 1) (centredCoverRefinement 1) 0) ∧
    realInterleavingDistance
        (mapperHomologyPModule ℚ flatMap (centredCover 1) (centredCoverRefinement 1) 0)
        (mapperHomologyPModule ℚ steepMap (centredCover 1) (centredCoverRefinement 1) 0) ≤
      (4 : ℝ≥0) := by
  have hflat : Module.finrank ℚ ((mapperHomologyPModule ℚ flatMap (centredCover 1)
      (centredCoverRefinement 1) 0).obj (1 / 2)) = 1 := by
    refine (finrank_scaleMap_centredCover_half 0 {0} fun k => ?_).trans (by simp)
    simp only [Finset.mem_singleton, zero_mul, mem_centredCover_half_iff, exists_const]
    constructor
    · rintro rfl
      norm_num
    · rintro ⟨h₁, h₂⟩
      have h₁' : (k : ℝ) < 1 := by linarith
      have h₂' : (-1 : ℝ) < k := by linarith
      have : k < 1 := by exact_mod_cast h₁'
      have : -1 < k := by exact_mod_cast h₂'
      omega
  have hsteep : Module.finrank ℚ ((mapperHomologyPModule ℚ steepMap (centredCover 1)
      (centredCoverRefinement 1) 0).obj (1 / 2)) = 5 := by
    refine (finrank_scaleMap_centredCover_half 4 (Finset.Icc 0 4) fun k => ?_).trans (by rfl)
    simp only [Finset.mem_Icc, mem_centredCover_half_iff]
    constructor
    · rintro ⟨h₀, h₄⟩
      have h₀' : (0 : ℝ) ≤ k := by exact_mod_cast h₀
      have h₄' : (k : ℝ) ≤ 4 := by exact_mod_cast h₄
      refine ⟨⟨(k : ℝ) / 4, ⟨by linarith, by linarith⟩⟩, ?_⟩
      constructor <;> simp only [] <;> linarith
    · rintro ⟨x, h₁, h₂⟩
      have hx₀ := x.2.1
      have hx₁ := x.2.2
      have h₁' : (k : ℝ) < 5 := by linarith
      have h₂' : (-1 : ℝ) < k := by linarith
      have : k < 5 := by exact_mod_cast h₁'
      have : -1 < k := by exact_mod_cast h₂'
      omega
  refine ⟨hflat, hsteep, ⟨fun e => ?_⟩, ?_⟩
  · have h := (e.app (1 / 2)).toLinearEquiv.finrank_eq
    rw [hflat, hsteep] at h
    exact absurd h (by norm_num)
  · exact realInterleavingDistance_centredMapperHomology_le ℚ 1 flat_steep_dist 0

/-! ## Pullback along the identity -/

/-- For the identity map, the pulled-back tower is the original tower and the pullback form of
the Mapper homology module is the direct form. -/
theorem pullback_id_mapperHomologyPModule {X : Type u} [TopologicalSpace X] (R : Type c)
    [Ring R] {Index : ℝ → Type w} (U : (t : ℝ) → Index t → Set X)
    [hU : ∀ t, LinearOrder (ComponentIndex (ContinuousMap.id X) (U t))]
    (rU : ∀ {s t : ℝ}, s ≤ t → Refinement (U s) (U t)) (n : ℕ) :
    (fun t => pullback (ContinuousMap.id X) (U t)) = U ∧
    mapperHomologyPModule R (ContinuousMap.id X) U rU n =
      @mapperHomologyPModule X X ℝ _ _ _ R _ (ContinuousMap.id X) Index
        (fun t => pullback (ContinuousMap.id X) (U t)) hU
        (fun h => pullbackRefinement (ContinuousMap.id X) (rU h)) n :=
  ⟨rfl, mapperHomologyPModule_pullback R (ContinuousMap.id X) U rU n⟩

/-! ## Negative control -/

/-- Any two refinements of one family pair induce the same `H₀` map, while the two simplicial
maps from a point to two isolated vertices, which are not induced by refinements of one family
pair, have different `H₀` maps over `ZMod 2`. The interleaving equations rest on the cover maps
being refinements. -/
theorem refinement_homology_control :
    (∀ r r' : Refinement selectorSource selectorTarget,
      mapperHomologyMap ℚ threeStageMap r 0 = mapperHomologyMap ℚ threeStageMap r' 0) ∧
    simplicialHomologyMap (ZMod 2) (mapToIsolated false) 0 ≠
      simplicialHomologyMap (ZMod 2) (mapToIsolated true) 0 :=
  ⟨fun r r' => mapperHomologyMap_eq ℚ threeStageMap r r' 0,
    isolated_vertex_maps_homology_ne.2⟩

end

end TDA.Mapper.RefinementHomologyInterleavingExamples
