import TDA.Persistence.FiniteSimplicialErosionScaling

/-!
# Exact erosion distance of two uniformly scaled tetrahedron-boundary modules

For reals `c, c' > 0`, the uniform scalings `scaledHomology k (fun _ => c) _` and
`scaledHomology k (fun _ => c') _` are two nonzero degree-one homology modules of the
tetrahedron-boundary grading with scaled lifetimes `c` and `c'`. Their weak-pair and
extended-rank erosion distances both equal
`ENNReal.ofReal (min (2 * |c - c'|) (max c c' / 2))`.

Upper bounds come from two independent arguments. Every literal face grade lies in `[0, 2]`,
so the grade error of two uniform scalings is `2 |c - c'|`, which bounds the distance through
`rankErosionDistance_finiteSimplicialHomology_le`. Independently, once `2ε` reaches both scaled
lifetimes every widened rank of either module vanishes, which bounds the distance by
`max c c' / 2`; this cap holds for anisotropic scales as well.

The lower bound uses actual rank tests, not the interleaving distance. For `c < c'`, a radius
`ε` below both `2 (c' - c)` and `c' / 2` fails the second erosion inequality at the diagonal
pair `a = b = (max (2 c) (c' + ε), ε)`: the widened map of the `c'`-module is nonzero on its
second arm, while the fibre of the `c`-module at `a` is zero because `2 c ≤ a 0`.

The closed formula is for uniform scales only. The cap lemma is stated for general scales, but
no distance formula is claimed for anisotropic scales.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory CategoryTheory.Limits TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal

/-- Every literal face grade of the tetrahedron boundary lies in `[0, 2]`. -/
theorem boundaryTetrahedronGrading_grade_mem_Icc
    (σ : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    boundaryTetrahedronGrading.grade σ i ∈ Set.Icc (0 : ℝ) 2 := by
  have h : boundaryTetrahedronGrading.grade σ i ∈
      boundaryTetrahedronGrading.gridCoordinates i :=
    (boundaryTetrahedronGrading.gridPoint σ i).2
  rw [boundaryTetrahedronGrading_gridCoordinates] at h
  have h' : boundaryTetrahedronGrading.grade σ i = 0 ∨
      boundaryTetrahedronGrading.grade σ i = 1 ∨
      boundaryTetrahedronGrading.grade σ i = 2 := by
    simpa only [grid, gridValues, Finset.mem_insert, Finset.mem_singleton] using h
  rcases h' with h | h | h <;> rw [h] <;> norm_num

/-- Two positive scalings differ at each face coordinate by at most twice the scale gap. -/
theorem scaledGrading_grade_error (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i)
    (s' : Fin 2 → ℝ) (hs' : ∀ i, 0 < s' i)
    (σ : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    |(scaledGrading s hs).grade σ i - (scaledGrading s' hs').grade σ i| ≤
      2 * |s i - s' i| := by
  obtain ⟨h0, h2⟩ := boundaryTetrahedronGrading_grade_mem_Icc σ i
  rw [scaledGrading_grade, scaledGrading_grade, ← sub_mul, abs_mul, abs_of_nonneg h0]
  nlinarith [abs_nonneg (s i - s' i)]

/-- Uniform scalings by `c` and `c'` have coordinatewise grade error at most `2 |c - c'|`. -/
theorem scaledGrading_const_grade_error (c : ℝ) (hc : 0 < c) (c' : ℝ) (hc' : 0 < c') :
    ∀ σ i, |(scaledGrading (fun _ => c) (fun _ => hc)).grade σ i -
      (scaledGrading (fun _ => c') (fun _ => hc')).grade σ i| ≤
        (Real.toNNReal (2 * |c - c'|) : ℝ) := by
  intro σ i
  rw [Real.coe_toNNReal _ (mul_nonneg zero_le_two (abs_nonneg _))]
  exact scaledGrading_grade_error _ _ _ _ σ i

/-- The maximal grade error of two uniform scalings is exactly `2 |c - c'|`. -/
theorem supGradeError_scaledGrading_const (c : ℝ) (hc : 0 < c) (c' : ℝ) (hc' : 0 < c') :
    (scaledGrading (fun _ => c) (fun _ => hc)).supGradeError
        (scaledGrading (fun _ => c') (fun _ => hc')) =
      Real.toNNReal (2 * |c - c'|) := by
  refine le_antisymm (((scaledGrading _ _).supGradeError_le_iff _ _).mpr
    (scaledGrading_const_grade_error c hc c' hc')) ?_
  obtain ⟨σ, hσ⟩ : ∃ σ, boundaryTetrahedronGrading.grade σ 0 = 2 := by
    classical
    have h2 : (2 : ℝ) ∈ boundaryTetrahedronGrading.gridCoordinates 0 := by
      rw [boundaryTetrahedronGrading_gridCoordinates]
      simp [grid, gridValues]
    change (2 : ℝ) ∈ insert 0 (Finset.univ.image
      (fun s : TotalFace boundaryTetrahedron.toPre => boundaryTetrahedronGrading.grade s 0)) at h2
    rcases Finset.mem_insert.mp h2 with h | h
    · norm_num at h
    · obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp h
      exact ⟨σ, hσ⟩
  have h := (scaledGrading (fun _ => c) (fun _ => hc)).abs_grade_sub_le_supGradeError
    (scaledGrading (fun _ => c') (fun _ => hc')) σ 0
  rw [scaledGrading_grade, scaledGrading_grade, hσ, ← sub_mul, abs_mul] at h
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (mul_nonneg zero_le_two (abs_nonneg _))]
  norm_num at h
  linarith

/-- A uniform scaling has scaled lifetime equal to its scale. -/
theorem scaledLifetime_const (c : ℝ) (hc : 0 ≤ c) :
    scaledLifetime (fun _ : Fin 2 => c) = c := by
  simp only [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB]
  rw [min_eq_right (by linarith), min_eq_left (by linarith), max_self]

private theorem rankOfStructureMap_eq_zero_of_structureMap_eq_zero {k : Type u} [Field k]
    (M : PModule.{u,0,u} k (Fin 2 → ℝ)) {p q : Fin 2 → ℝ} (hpq : p ≤ q)
    (h : structureMap M hpq = 0) : rankOfStructureMap M hpq = 0 := by
  unfold rankOfStructureMap
  have hlin : structureMapLinear M hpq = 0 := by
    simp [structureMapLinear, h]
  rw [hlin, LinearMap.range_zero, finrank_bot]

private theorem scaledHomology_rank_erosionWide_eq_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (ε : ℝ≥0)
    (hε : scaledLifetime s ≤ 2 * (ε : ℝ)) {a b : Fin 2 → ℝ} (hab : a ≤ b) :
    rankOfStructureMap (scaledHomology k s hs) (erosionWide_le ε hab) = 0 := by
  have h1 : erosionLower ε a ≤ fun i => erosionLower ε a i + 2 * (ε : ℝ) :=
    fun _ => le_add_of_nonneg_right (by positivity)
  have h2 : (fun i => erosionLower ε a i + 2 * (ε : ℝ)) ≤ erosionUpper ε b := by
    intro i
    simp only [erosionLower, erosionUpper]
    linarith [hab i]
  have hle := rankOfStructureMap_four_point (scaledHomology k s hs) (le_refl _) h1 h2
  rw [rankOfStructureMap_eq_zero_of_structureMap_eq_zero _ h1
    (scaledHomology_lifetime_structureMap_zero k s hs _ hε _)] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Any two positive scalings satisfy erosion at every radius whose double reaches both scaled
lifetimes: every widened rank of either module vanishes. -/
theorem scaledHomology_rankErosion_of_scaledLifetime_le (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (s' : Fin 2 → ℝ) (hs' : ∀ i, 0 < s' i)
    (ε : ℝ≥0) (h : scaledLifetime s ≤ 2 * (ε : ℝ)) (h' : scaledLifetime s' ≤ 2 * (ε : ℝ)) :
    RankErosion ε (scaledHomology k s hs) (scaledHomology k s' hs') := by
  constructor <;> intro a b hab
  · rw [scaledHomology_rank_erosionWide_eq_zero k s hs ε h hab]
    exact Nat.zero_le _
  · rw [scaledHomology_rank_erosionWide_eq_zero k s' hs' ε h' hab]
    exact Nat.zero_le _

/-- Any two positive scalings satisfy extended-rank erosion at every radius whose double reaches
both scaled lifetimes. -/
theorem scaledHomology_eRankErosion_of_scaledLifetime_le (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (s' : Fin 2 → ℝ) (hs' : ∀ i, 0 < s' i)
    (ε : ℝ≥0) (h : scaledLifetime s ≤ 2 * (ε : ℝ)) (h' : scaledLifetime s' ≤ 2 * (ε : ℝ)) :
    ERankErosion ε (scaledHomology k s hs) (scaledHomology k s' hs') :=
  eRankErosion_iff_rankErosion.mpr
    (scaledHomology_rankErosion_of_scaledLifetime_le k s hs s' hs' ε h h')

/-- For `c < c'`, below `2 (c' - c)` and half of `c'`, erosion fails at the diagonal pair
`a = (max (2c) (c' + ε), ε)`: the widened map of the `c'`-module survives on its B-arm, while
the fibre of the `c`-module at `a` is zero because `2c ≤ a 0`. -/
theorem scaledHomology_const_not_rankErosion_of_lt (k : Type u) [Field k]
    (c : ℝ) (hc : 0 < c) (c' : ℝ) (hc' : 0 < c') (ε : ℝ≥0)
    (hgap : (ε : ℝ) < 2 * (c' - c)) (hcap : 2 * (ε : ℝ) < c') :
    ¬ RankErosion ε (scaledHomology k (fun _ => c) (fun _ => hc))
      (scaledHomology k (fun _ => c') (fun _ => hc')) := by
  rintro ⟨-, h⟩
  have hε0 : (0 : ℝ) ≤ ε := ε.coe_nonneg
  let a : Fin 2 → ℝ := fun i => if i = 0 then max (2 * c) (c' + ε) else (ε : ℝ)
  have hle := h a a le_rfl
  have hzero : rankOfStructureMap (scaledHomology k (fun _ => c) (fun _ => hc))
      (le_refl a) = 0 := by
    apply rankOfStructureMap_eq_zero_of_isZero
    have hmap : structureMap (scaledHomology k (fun _ => c) (fun _ => hc)) (le_refl a) = 0 := by
      by_contra hne
      obtain ⟨-, -, -, h0, -⟩ :=
        (scaledHomology_structureMap_ne_zero_iff k _ _ (le_refl a)).1 hne
      simp only [a, ↓reduceIte] at h0
      linarith [le_max_left (2 * c) (c' + ε)]
    rw [IsZero.iff_id_eq_zero, ← structureMap_self _ (le_refl a)]
    exact hmap
  have hpos : 1 ≤ rankOfStructureMap (scaledHomology k (fun _ => c') (fun _ => hc'))
      (erosionWide_le ε (le_refl a)) := by
    apply one_le_rankOfStructureMap_of_ne_zero
    rw [scaledHomology_structureMap_ne_zero_iff]
    have hA := le_max_right (2 * c) (c' + ε)
    have hB : max (2 * c) (c' + ε) + ε < 2 * c' := by
      have := max_lt (show 2 * c < 2 * c' - ε by linarith)
        (show c' + ε < 2 * c' - ε by linarith)
      linarith
    simp only [erosionLower, erosionUpper, a, Fin.isValue, ↓reduceIte,
      show (1 : Fin 2) ≠ 0 by decide]
    refine ⟨by linarith, by linarith, Or.inl (by linarith), hB, by linarith⟩
  omega

/-- Two uniform scalings fail weak-pair rank erosion at every radius strictly below
`min (2 |c - c'|) (max c c' / 2)`. -/
theorem scaledHomology_const_not_rankErosion (k : Type u) [Field k]
    (c : ℝ) (hc : 0 < c) (c' : ℝ) (hc' : 0 < c') (ε : ℝ≥0)
    (hε : (ε : ℝ) < min (2 * |c - c'|) (max c c' / 2)) :
    ¬ RankErosion ε (scaledHomology k (fun _ => c) (fun _ => hc))
      (scaledHomology k (fun _ => c') (fun _ => hc')) := by
  have hgap : (ε : ℝ) < 2 * |c - c'| := hε.trans_le (min_le_left _ _)
  have hcap : (ε : ℝ) < max c c' / 2 := hε.trans_le (min_le_right _ _)
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · apply scaledHomology_const_not_rankErosion_of_lt k c hc c' hc' ε
    · rwa [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)] at hgap
    · rw [max_eq_right hlt.le] at hcap
      linarith
  · subst heq
    simp only [sub_self, abs_zero, mul_zero] at hgap
    exact absurd hgap (not_lt.mpr ε.coe_nonneg)
  · intro h
    refine scaledHomology_const_not_rankErosion_of_lt k c' hc' c hc ε ?_ ?_ h.symm
    · rwa [abs_of_pos (sub_pos.mpr hgt)] at hgap
    · rw [max_eq_left hgt.le] at hcap
      linarith

/-- Two uniform scalings fail extended-rank erosion below the same value. -/
theorem scaledHomology_const_not_eRankErosion (k : Type u) [Field k]
    (c : ℝ) (hc : 0 < c) (c' : ℝ) (hc' : 0 < c') (ε : ℝ≥0)
    (hε : (ε : ℝ) < min (2 * |c - c'|) (max c c' / 2)) :
    ¬ ERankErosion ε (scaledHomology k (fun _ => c) (fun _ => hc))
      (scaledHomology k (fun _ => c') (fun _ => hc')) := by
  rw [eRankErosion_iff_rankErosion]
  exact scaledHomology_const_not_rankErosion k c hc c' hc' ε hε

/-- The weak-pair rank erosion distance of two uniform scalings is exactly
`min (2 |c - c'|) (max c c' / 2)`. -/
theorem rankErosionDistance_scaledHomology_const (k : Type u) [Field k]
    (c : ℝ) (hc : 0 < c) (c' : ℝ) (hc' : 0 < c') :
    rankErosionDistance (scaledHomology k (fun _ => c) (fun _ => hc))
      (scaledHomology k (fun _ => c') (fun _ => hc')) =
        ENNReal.ofReal (min (2 * |c - c'|) (max c c' / 2)) := by
  apply le_antisymm
  · rcases le_total (2 * |c - c'|) (max c c' / 2) with hm | hm
    · rw [min_eq_left hm]
      exact rankErosionDistance_finiteSimplicialHomology_le k _ _ 1
        (scaledGrading_const_grade_error c hc c' hc')
    · rw [min_eq_right hm]
      have hnn : 0 ≤ max c c' / 2 := div_nonneg (le_max_of_le_left hc.le) zero_le_two
      refine rankErosionDistance_le_of_erosion
        (scaledHomology_rankErosion_of_scaledLifetime_le k _ _ _ _ _ ?_ ?_)
      · rw [scaledLifetime_const c hc.le, Real.coe_toNNReal _ hnn]
        linarith [le_max_left c c']
      · rw [scaledLifetime_const c' hc'.le, Real.coe_toNNReal _ hnn]
        linarith [le_max_right c c']
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    exact le_rankErosionDistance_of_not_rankErosion
      (scaledHomology_const_not_rankErosion k c hc c' hc' r (ENNReal.coe_lt_ofReal.mp hr))

/-- The extended-rank erosion distance of two uniform scalings is exactly
`min (2 |c - c'|) (max c c' / 2)`. -/
theorem eRankErosionDistance_scaledHomology_const (k : Type u) [Field k]
    (c : ℝ) (hc : 0 < c) (c' : ℝ) (hc' : 0 < c') :
    eRankErosionDistance (scaledHomology k (fun _ => c) (fun _ => hc))
      (scaledHomology k (fun _ => c') (fun _ => hc')) =
        ENNReal.ofReal (min (2 * |c - c'|) (max c c' / 2)) := by
  rw [eRankErosionDistance_eq_rankErosionDistance, rankErosionDistance_scaledHomology_const]

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
