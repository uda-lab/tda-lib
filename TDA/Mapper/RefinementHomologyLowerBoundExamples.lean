import TDA.Mapper.RefinementHomologyLowerBound
import TDA.Mapper.RefinementHomologyInterleavingExamples
import TDA.Mapper.RefinementHomologyBarcodeExamples
import TDA.Simplicial.H0Augmentation

/-!
# Rank-obstruction fixtures for Mapper interleaving distances

* **Exact distance `1`.** Over the one-point space, the towers whose single member is the whole
  space for radii strictly greater than `1`, respectively `0`, and empty at and below that
  radius, have degree-zero Mapper homology
  modules at real interleaving distance exactly `1` over every field. Cover maps shifting by `1`
  give the upper bound; for `ε < 1` the second module has a nonzero structure map from `1 - ε`
  to `1 + ε`, while the first module is zero at `1`.
* **Flat and steep maps.** Along the centred tower of spacing `1`, the constant map `0` and the
  map `x ↦ 4x` on the unit interval have degree-zero Mapper homology modules over `ℚ` at real
  interleaving distance between `1/8` and `4`. At every radius in `(0, 1/2]` the Mapper
  complexes have no edges, the flat `H₀` has dimension `1` and the steep `H₀` has dimension
  `5`, and the steep refinement maps between such radii are isomorphisms on `H₀`.
* **Isomorphic modules.** For a module and itself with the identity `0`-interleaving, every rank
  inequality holds, the hypothesis of the distance lower bound fails at `ε = 0`, and the distance
  is `0`.
* **Negative control.** For the constant map from discrete `ℕ` with one full member, every value
  of the degree-zero module is infinite-dimensional, so the rank bound does not apply;
  `Module.finrank` is `0` there by convention and no inequality is asserted.
-/

namespace TDA.Mapper.RefinementHomologyLowerBoundExamples

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence
open TDA.Mapper.TowerExamples
open TDA.Mapper.RefinementHomologyExamples
open TDA.Mapper.RefinementHomologyInterleavingExamples
open scoped NNReal ENNReal unitInterval

noncomputable section

universe u v w c

/-! ## Bijective Mapper maps into edgeless complexes -/

section Bijective

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (R : Type c)
  [Ring R] (f : C(X, Y)) {ι κ : Type w} {U : ι → Set Y} {V : κ → Set Y}
  [LinearOrder (ComponentIndex f U)] [LinearOrder (ComponentIndex f V)]

private theorem eq_singleton_of_no_edges [IsEmpty (Face (mapper f V) 1)]
    {s : Finset (ComponentIndex f V)} (hs : s ∈ mapper f V) : ∃ b, s = {b} := by
  obtain ⟨hne, x, hx⟩ := (mem_mapper_iff f V s).1 hs
  refine Finset.card_eq_one.1 (le_antisymm ?_ hne.card_pos)
  by_contra hlt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (not_le.1 hlt)
  have hface : ({a, b} : Finset (ComponentIndex f V)) ∈ mapper f V :=
    (mem_mapper_iff f V _).2 ⟨Finset.insert_nonempty _ _, x, fun d hd => by
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact hx _ ha
      · rw [Finset.mem_singleton.1 hd]
        exact hx _ hb⟩
  exact isEmptyElim (⟨_, hface, Finset.card_pair hab⟩ : Face (mapper f V) 1)

/-- The inverse of a bijective Mapper vertex map into an edgeless Mapper complex, as a vertex
map. -/
private def inverseVertexMap [IsEmpty (Face (mapper f V) 1)] (r : Refinement U V)
    (hr : Function.Bijective (mapperMap f r)) : VertexMap (mapper f V) (mapper f U) where
  toFun := (Equiv.ofBijective _ hr).symm
  map_face s hs := by
    obtain ⟨b, rfl⟩ := eq_singleton_of_no_edges f hs
    rw [@Finset.image_singleton _ _ (Classical.decEq _)]
    exact componentIndex_supported f U _

/-- If the Mapper vertex map of a refinement is bijective and the target Mapper complex has no
edges, then the induced homology map is bijective in every degree. -/
theorem mapperHomologyMap_bijective_of_bijective [IsEmpty (Face (mapper f V) 1)]
    (r : Refinement U V) (hr : Function.Bijective (mapperMap f r)) (n : ℕ) :
    Function.Bijective (mapperHomologyMap R f r n).hom := by
  let g := inverseVertexMap f r hr
  have h₁ : mapperHomologyMap R f r n ≫ simplicialHomologyMap R g n = 𝟙 _ := by
    rw [mapperHomologyMap_def, ← simplicialHomologyMap_comp]
    convert simplicialHomologyMap_id R (mapper f U) n
    exact VertexMap.ext fun a => (Equiv.ofBijective _ hr).symm_apply_apply a
  have h₂ : simplicialHomologyMap R g n ≫ mapperHomologyMap R f r n = 𝟙 _ := by
    rw [mapperHomologyMap_def, ← simplicialHomologyMap_comp]
    convert simplicialHomologyMap_id R (mapper f V) n
    exact VertexMap.ext fun b => (Equiv.ofBijective _ hr).apply_symm_apply b
  refine Function.bijective_iff_has_inverse.2 ⟨(simplicialHomologyMap R g n).hom, ?_, ?_⟩
  · intro x
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h₁) x
  · intro y
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h₂) y

end Bijective

/-! ## Exact distance of two shifted one-member towers -/

section Shifted

local instance {ι : Type} [LinearOrder ι] (U : ι → Set Unit) :
    LinearOrder (ComponentIndex threeStageMap U) :=
  componentIndexLinearOrder threeStageMap U

/-- The one-point space as the only member for radii strictly greater than `1`; the member is
empty at and below `1`. -/
def lateTower (t : ℝ) : Unit → Set Unit := fun _ => {_x | 1 < t}

/-- The one-point space as the only member for radii strictly greater than `0`; the member is
empty at and below `0`. -/
def earlyTower (t : ℝ) : Unit → Set Unit := fun _ => {_x | 0 < t}

/-- The identity-selector refinements of the late tower. -/
def lateRefinement {s t : ℝ} (h : s ≤ t) : Refinement (lateTower s) (lateTower t) where
  selector i := i
  subset _ _ hx := lt_of_lt_of_le hx h

/-- The identity-selector refinements of the early tower. -/
def earlyRefinement {s t : ℝ} (h : s ≤ t) : Refinement (earlyTower s) (earlyTower t) where
  selector i := i
  subset _ _ hx := lt_of_lt_of_le hx h

/-- Identity-selector cover maps from the late tower into the early tower shifted by `η`. -/
def lateToEarly (η : ℝ≥0) (t : ℝ) : Refinement (lateTower t) (earlyTower (t + η)) where
  selector i := i
  subset _ _ hx := by
    change 0 < t + (η : ℝ)
    have : 1 < t := hx
    linarith [η.coe_nonneg]

/-- Identity-selector cover maps from the early tower into the late tower shifted by `1`. -/
def earlyToLate (t : ℝ) : Refinement (earlyTower t) (lateTower (t + (1 : ℝ≥0))) where
  selector i := i
  subset _ _ hx := by
    change 1 < t + ((1 : ℝ≥0) : ℝ)
    have : 0 < t := hx
    simp only [NNReal.coe_one]
    linarith

private theorem lateTower_componentIndex_isEmpty {t : ℝ} (ht : ¬ 1 < t) :
    IsEmpty (ComponentIndex threeStageMap (lateTower t)) :=
  ⟨fun a => by
    induction a.2 using ZerothHomotopy.rec with
    | mk x => exact ht x.2⟩

/-- Over every field, the refinement map of the early tower between positive radii is nonzero
on `H₀`: it sends the nonzero class of the unique vertex to the class of the unique vertex. -/
theorem mapperHomologyMap_earlyRefinement_ne_zero (k : Type c) [Field k] {s t : ℝ}
    (hs : 0 < s) (h : s ≤ t) :
    mapperHomologyMap k threeStageMap (earlyRefinement h) 0 ≠ 0 :=
  mapperHomologyMap_zero_ne_zero k (earlyRefinement h)
    ⟨(), ZerothHomotopy.mk ⟨(), hs⟩⟩

/-- Over every field, the degree-zero Mapper homology modules of the late and early towers are
at real interleaving distance exactly `1`. -/
theorem realInterleavingDistance_late_early (k : Type c) [Field k] :
    realInterleavingDistance
        (mapperHomologyPModule k threeStageMap lateTower lateRefinement 0)
        (mapperHomologyPModule k threeStageMap earlyTower earlyRefinement 0) = 1 := by
  apply le_antisymm
  · simpa using realInterleavingDistance_mapperHomologyPModule_le k threeStageMap
      lateRefinement earlyRefinement 0 (lateToEarly 1) earlyToLate
  · rw [realInterleavingDistance_comm]
    refine le_realInterleavingDistance_mapperHomologyPModule_of_isEmpty_face k
      earlyRefinement lateRefinement 0 fun ε hε => ?_
    have hε' : (ε : ℝ) < 1 := by exact_mod_cast hε
    have hpos : 0 < 1 - (ε : ℝ) := by linarith
    refine ⟨1 - ε, by linarith [ε.coe_nonneg], ?_,
      mapperHomologyMap_earlyRefinement_ne_zero k hpos _⟩
    have := lateTower_componentIndex_isEmpty (t := 1 - (ε : ℝ) + ε) (by simp)
    exact isEmpty_face_mapper threeStageMap _ 0

end Shifted

/-! ## A positive lower bound for the flat and steep maps -/

section FlatSteep

attribute [local instance] scaleMapComponentOrder

/-- For radii at most `1/2`, the Mapper complex of a real-valued map along the centred family
of spacing `1` has no edges, since its members are pairwise disjoint. -/
theorem centredCover_no_edges_of_le_half {X : Type} [TopologicalSpace X] (f : C(X, ℝ))
    {t : ℝ} (ht : t ≤ 1 / 2) [LinearOrder (ComponentIndex f (centredCover 1 t))] :
    IsEmpty (Face (mapper f (centredCover 1 t)) 1) := by
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

/-- For a scaled map whose values within `1/2` of an integer `k` force `k` to be attained,
the Mapper vertex map of the centred refinement between radii `0 < a ≤ b ≤ 1/2` is a
bijection. -/
private theorem mapperMap_scaleMap_bijective (c : ℝ)
    (hc : ∀ (x : I) (k : ℤ), |c * (x : ℝ) - k| < 1 / 2 → ∃ y : I, c * (y : ℝ) = k)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    Function.Bijective (mapperMap (scaleMap c) (centredCoverRefinement 1 hab)) := by
  constructor
  · rintro ⟨k, p⟩ ⟨l, q⟩ h
    have hkl : k = l := congrArg Sigma.fst h
    subst hkl
    have := scaleMap_zerothHomotopy_subsingleton c 1 a k
    exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim p q))
  · rintro ⟨k, p⟩
    induction p using ZerothHomotopy.rec with
    | mk x =>
    have hx : |c * (x.1 : ℝ) - k| < 1 / 2 := by
      have := mem_centredCover_iff.1 x.2
      simp only [mul_one] at this
      change |c * (x.1 : ℝ) - k| < b at this
      linarith
    obtain ⟨y, hy⟩ := hc x.1 k hx
    have hya : scaleMap c y ∈ centredCover 1 a k := by
      rw [mem_centredCover_iff]
      change |c * (y : ℝ) - k * 1| < a
      rw [hy, mul_one, sub_self, abs_zero]
      exact ha
    refine ⟨⟨k, ZerothHomotopy.mk ⟨y, hya⟩⟩, ?_⟩
    rw [mapperMap_mk]
    have := scaleMap_zerothHomotopy_subsingleton c 1 b k
    exact Sigma.ext rfl (heq_of_eq
      (Subsingleton.elim (α := ZerothHomotopy (PullbackSpace (scaleMap c) (centredCover 1 b) k))
        _ _))

private theorem flat_attains (x : I) (k : ℤ) (h : |0 * (x : ℝ) - k| < 1 / 2) :
    ∃ y : I, 0 * (y : ℝ) = k := by
  rw [zero_mul, zero_sub, abs_neg] at h
  have h' : |k| < 1 := by
    have : |(k : ℝ)| < 1 := by linarith
    exact_mod_cast this
  refine ⟨x, ?_⟩
  rw [zero_mul, eq_comm, Int.cast_eq_zero]
  exact Int.abs_lt_one_iff.1 h'

private theorem steep_attains (x : I) (k : ℤ) (h : |4 * (x : ℝ) - k| < 1 / 2) :
    ∃ y : I, 4 * (y : ℝ) = k := by
  rw [abs_lt] at h
  have hx₀ := x.2.1
  have hx₁ := x.2.2
  have hk₀ : (-1 : ℝ) < k := by linarith
  have hk₄ : (k : ℝ) < 5 := by linarith
  have hk₀' : 0 ≤ k := by
    have : (-1 : ℤ) < k := by exact_mod_cast hk₀
    omega
  have hk₄' : k ≤ 4 := by
    have : k < (5 : ℤ) := by exact_mod_cast hk₄
    omega
  have h₀ : (0 : ℝ) ≤ k := by exact_mod_cast hk₀'
  have h₄ : (k : ℝ) ≤ 4 := by exact_mod_cast hk₄'
  exact ⟨⟨(k : ℝ) / 4, by linarith, by linarith⟩,
    by change 4 * ((k : ℝ) / 4) = k; ring⟩

/-- The degree-zero refinement map of a scaled map along the centred tower between radii
`0 < a ≤ b ≤ 1/2` is bijective, under the attainment hypothesis of
`mapperMap_scaleMap_bijective`. -/
private theorem scaleMap_structureMap_bijective (c : ℝ)
    (hc : ∀ (x : I) (k : ℤ), |c * (x : ℝ) - k| < 1 / 2 → ∃ y : I, c * (y : ℝ) = k)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    Function.Bijective (mapperHomologyMap ℚ (scaleMap c) (centredCoverRefinement 1 hab) 0).hom :=
  have := centredCover_no_edges_of_le_half (scaleMap c) hb
  mapperHomologyMap_bijective_of_bijective ℚ (scaleMap c) _
    (mapperMap_scaleMap_bijective c hc ha hab hb) 0

private theorem finrank_scaleMap_eq_half (c : ℝ)
    (hc : ∀ (x : I) (k : ℤ), |c * (x : ℝ) - k| < 1 / 2 → ∃ y : I, c * (y : ℝ) = k)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) :
    Module.finrank ℚ (simplicialHomology (mapper (scaleMap c) (centredCover 1 r)) ℚ 0) =
      Module.finrank ℚ
        (simplicialHomology (mapper (scaleMap c) (centredCover 1 (1 / 2))) ℚ 0) :=
  (LinearEquiv.ofBijective _ (scaleMap_structureMap_bijective c hc hr hr' le_rfl)).finrank_eq

/-- At every radius in `(0, 1/2]`, `H₀` over `ℚ` of the flat map's Mapper complex along the
centred family of spacing `1` has dimension `1`. -/
theorem finrank_flat_centredCover {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) :
    Module.finrank ℚ (simplicialHomology (mapper flatMap (centredCover 1 r)) ℚ 0) = 1 :=
  (finrank_scaleMap_eq_half 0 flat_attains hr hr').trans flat_steep_perturbation.1

/-- At every radius in `(0, 1/2]`, `H₀` over `ℚ` of the steep map's Mapper complex along the
centred family of spacing `1` has dimension `5`. -/
theorem finrank_steep_centredCover {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) :
    Module.finrank ℚ (simplicialHomology (mapper steepMap (centredCover 1 r)) ℚ 0) = 5 :=
  (finrank_scaleMap_eq_half 4 steep_attains hr hr').trans flat_steep_perturbation.2.1

/-- Between radii `0 < a ≤ b ≤ 1/2`, the steep map's refinement map on `H₀` over `ℚ` along the
centred tower has rank `5`. -/
theorem finrank_range_steep_refinement {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    Module.finrank ℚ (LinearMap.range
      (mapperHomologyMap ℚ steepMap (centredCoverRefinement 1 hab) 0).hom) = 5 := by
  rw [LinearMap.range_eq_top.2 (scaleMap_structureMap_bijective 4 steep_attains ha hab hb).2,
    finrank_top]
  exact finrank_steep_centredCover (ha.trans_le hab) hb

/-- Along the centred tower of spacing `1`, the degree-zero Mapper homology modules over `ℚ` of
the flat and steep maps are at real interleaving distance at least `1/8` and at most `4`. -/
theorem flat_steep_distance_bounds :
    (1 / 8 : ℝ≥0∞) ≤ realInterleavingDistance
        (mapperHomologyPModule ℚ flatMap (centredCover 1) (centredCoverRefinement 1) 0)
        (mapperHomologyPModule ℚ steepMap (centredCover 1) (centredCoverRefinement 1) 0) ∧
    realInterleavingDistance
        (mapperHomologyPModule ℚ flatMap (centredCover 1) (centredCoverRefinement 1) 0)
        (mapperHomologyPModule ℚ steepMap (centredCover 1) (centredCoverRefinement 1) 0) ≤ 4 := by
  refine ⟨?_, by simpa using flat_steep_perturbation.2.2.2⟩
  rw [realInterleavingDistance_comm]
  refine le_realInterleavingDistance_centredMapperHomology_of_finrank_lt ℚ 1 0
    fun ε hε => ?_
  have hε' : (ε : ℝ) < 1 / 8 := by
    have : (ε : ℝ≥0∞) < ((1 / 8 : ℝ≥0) : ℝ≥0∞) := by simpa using hε
    exact_mod_cast ENNReal.coe_lt_coe.1 this
  have hε₀ := ε.coe_nonneg
  have h : (1 / 4 : ℝ) ≤ 1 / 4 + ((ε + ε : ℝ≥0) : ℝ) := by push_cast; linarith
  have hflat := finrank_flat_centredCover (r := 1 / 4 + ε) (by linarith) (by linarith)
  refine ⟨1 / 4, h, Module.finite_of_finrank_eq_succ hflat, ?_⟩
  rw [hflat, finrank_range_steep_refinement (by norm_num) h (by push_cast; linarith)]
  norm_num

end FlatSteep

/-! ## Isomorphic modules -/

/-- For a module and itself with the identity `0`-interleaving, every rank inequality of the
rank bound holds, the hypothesis of the distance lower bound fails at `ε = 0` at every
parameter, and the distance is `0`. -/
theorem rank_obstruction_self (k : Type u) [Field k] (M : PModule.{u,0,w} k ℝ) :
    (∀ (t : ℝ) (h : t ≤ t + ((0 + 0 : ℝ≥0) : ℝ))
        [FiniteDimensional k (M.obj (t + ((0 : ℝ≥0) : ℝ)))],
        Module.finrank k (LinearMap.range (structureMapLinear M h)) ≤
          Module.finrank k (M.obj (t + ((0 : ℝ≥0) : ℝ)))) ∧
    (∀ (t : ℝ) (h : t ≤ t + ((0 + 0 : ℝ≥0) : ℝ)),
      ¬ (FiniteDimensional k (M.obj (t + ((0 : ℝ≥0) : ℝ))) ∧
        Module.finrank k (M.obj (t + ((0 : ℝ≥0) : ℝ))) <
          Module.finrank k (LinearMap.range (structureMapLinear M h)))) ∧
    realInterleavingDistance M M = 0 := by
  refine ⟨fun t h _ => finrank_range_structureMapLinear_le_of_realInterleaving
    (RealInterleaving.refl 0 M) t h, fun t h ⟨_, hlt⟩ => ?_, realInterleavingDistance_self M⟩
  exact (isEmpty_realInterleaving_of_finrank_lt t h hlt).false (RealInterleaving.refl 0 M)

/-! ## Negative control: infinite-dimensional values -/

section NatComponents

open TDA.Mapper.GraphPL.Examples (natToUnit)
open TDA.Mapper.Examples (unitCover)
open TDA.Mapper.RefinementHomologyBarcodeExamples (natToUnit_not_finiteDimensional)

/-- For the constant map from discrete `ℕ` along the constant tower with one full member, every
value of the degree-zero Mapper homology module is infinite-dimensional over every field, for
every component order, so the rank bound does not apply; `Module.finrank` is `0` there by
convention. -/
theorem natToUnit_tower_not_finiteDimensional
    [LinearOrder (ComponentIndex natToUnit unitCover)] (k : Type) [Field k] (t : ℝ) :
    ¬ FiniteDimensional k ((mapperHomologyPModule k natToUnit (fun _ : ℝ => unitCover)
        (fun _ => Refinement.id unitCover) 0).obj t) ∧
      Module.finrank k ((mapperHomologyPModule k natToUnit (fun _ : ℝ => unitCover)
        (fun _ => Refinement.id unitCover) 0).obj t) = 0 :=
  ⟨natToUnit_not_finiteDimensional k, Module.finrank_of_not_finite
    (natToUnit_not_finiteDimensional k)⟩

end NatComponents

end

end TDA.Mapper.RefinementHomologyLowerBoundExamples
