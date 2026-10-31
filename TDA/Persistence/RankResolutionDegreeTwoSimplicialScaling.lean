import TDA.Persistence.RankResolutionDegreeTwoSimplicialTranslation
import TDA.Persistence.FiniteSimplicialInterleaving

/-!
# Positive independent scaling of the simplicial witness

Positive scaling of each face-grade coordinate reindexes the actual
degree-one homology module by a coordinate order isomorphism. Its armwise
diagonal lifetimes determine the exact distance of the full PH₁ module to zero.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory CategoryTheory.Limits TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal ZeroObject

/-- Divide each real grade coordinate by its positive face scale. -/
noncomputable def scalingPullback (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    (Fin 2 → ℝ) →o (Fin 2 → ℝ) :=
  OrderHom.pi (fun i =>
    OrderHomClass.toOrderHom (OrderIso.divRight₀ (s i) (hs i)) |>.comp
      (Pi.evalOrderHom i))

@[simp] theorem scalingPullback_apply (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i)
    (p : Fin 2 → ℝ) (i : Fin 2) :
    scalingPullback s hs p i = p i / s i := by
  simp [scalingPullback]

/-- Multiply each actual face-grade coordinate by its positive scale. -/
def scaledGrading (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    FiniteGraded boundaryTetrahedron 2 where
  grade σ i := s i * boundaryTetrahedronGrading.grade σ i
  mono h i := mul_le_mul_of_nonneg_left
    (boundaryTetrahedronGrading.mono h i) (le_of_lt (hs i))

@[simp] theorem scaledGrading_grade (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i)
    (σ : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    (scaledGrading s hs).grade σ i = s i * boundaryTetrahedronGrading.grade σ i := rfl

/-- Unit scaling recovers the literal unmodified face grading. -/
theorem scaledGrading_one :
    scaledGrading (fun _ : Fin 2 => (1 : ℝ)) (fun _ => by norm_num) =
      boundaryTetrahedronGrading := by
  apply FiniteGraded.ext
  intro σ
  funext i
  simp [scaledGrading]

/-- Positive scaling is exactly pullback of the original sublevel grade. -/
theorem scaledGrading_sublevel (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i)
    (p : Fin 2 → ℝ) :
    (scaledGrading s hs).sublevel p =
      boundaryTetrahedronGrading.sublevel (scalingPullback s hs p) := by
  apply le_antisymm
  · rintro σ ⟨hσ, hp⟩
    refine ⟨hσ, fun i => ?_⟩
    change boundaryTetrahedronGrading.grade ⟨σ, hσ⟩ i ≤ p i / s i
    apply (le_div_iff₀ (hs i)).2
    simpa [mul_comm] using hp i
  · rintro σ ⟨hσ, hp⟩
    refine ⟨hσ, fun i => ?_⟩
    change s i * boundaryTetrahedronGrading.grade ⟨σ, hσ⟩ i ≤ p i
    have hpi : boundaryTetrahedronGrading.grade ⟨σ, hσ⟩ i ≤ p i / s i := hp i
    have hi := (le_div_iff₀ (hs i)).1 hpi
    simpa [mul_comm] using hi

/-- The actual PH₁ persistence module of the positively scaled face filtration. -/
noncomputable abbrev scaledHomology (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) : PModule.{u,0,u} k (Fin 2 → ℝ) :=
  finiteSimplicialHomology k (scaledGrading s hs) 1

/-- Unit scaling recovers the literal unmodified PH₁ module. -/
theorem scaledHomology_one (k : Type u) [Field k] :
    scaledHomology k (fun _ : Fin 2 => (1 : ℝ)) (fun _ => by norm_num) =
      finiteSimplicialHomology k boundaryTetrahedronGrading 1 := by
  simp only [scaledHomology, scaledGrading_one]

/-- The actual scaled PH₁ module is naturally reindexed from the original one. -/
noncomputable def scaledHomologyReindexIso (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    scaledHomology k s hs ≅
      reindex (scalingPullback s hs)
        (finiteSimplicialHomology k boundaryTetrahedronGrading 1) := by
  have hfil : (scaledGrading s hs).sublevelFiltration =
      TDA.Filtration.reindex (scalingPullback s hs)
        boundaryTetrahedronGrading.sublevelFiltration := by
    apply DFunLike.ext
    intro p
    exact scaledGrading_sublevel s hs p
  unfold scaledHomology finiteSimplicialHomology
  rw [hfil]
  exact Iso.refl _

/-- The scaled realization is the original actual PH₁ realization reindexed
by coordinatewise division. -/
noncomputable def scaledRealIso (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    scaledHomology k s hs ≅
      reindex (scalingPullback s hs) (realModule (k := k)) :=
  (scaledHomologyReindexIso k s hs).trans
    (Functor.isoWhiskerLeft (scalingPullback s hs).toFunctor (realIso k))

/-- The realization isomorphism preserves every actual inclusion-induced
structure map under the scaling pullback. -/
theorem scaledRealIso_structureMap (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (scaledHomology k s hs) hpq ≫ (scaledRealIso k s hs).hom.app q =
      (scaledRealIso k s hs).hom.app p ≫
        structureMap (realModule (k := k)) ((scalingPullback s hs).monotone' hpq) :=
  (scaledRealIso k s hs).hom.naturality (homOfLE hpq)

/-- Finite presentation follows from the actual scaled finite-simplicial input. -/
theorem scaledHomology_finitelyPresented (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (scaledHomology k s hs) :=
  finiteSimplicialHomology_finitelyPresented k (scaledGrading s hs) 1

private theorem map_zero_of_iso {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} (e : M ≅ N)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) (hz : structureMap N hpq = 0) :
    structureMap M hpq = 0 := by
  apply (cancel_mono (e.hom.app q)).mp
  have hn := e.hom.naturality (homOfLE hpq)
  change structureMap M hpq ≫ e.hom.app q = e.hom.app p ≫ structureMap N hpq at hn
  rw [hn, hz, comp_zero, zero_comp]

private theorem map_ne_zero_of_iso {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} (e : M ≅ N)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) (hne : structureMap N hpq ≠ 0) :
    structureMap M hpq ≠ 0 := by
  intro hz
  exact hne (map_zero_of_iso e.symm hpq hz)

/-- Positive scaling transports the actual-map characteristic through the
coordinate reindexing. -/
theorem scaledHomology_structureMap_ne_zero_iff (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (scaledHomology k s hs) hpq ≠ 0 ↔
      0 ≤ p 0 ∧ 0 ≤ p 1 ∧ (s 0 ≤ p 0 ∨ s 1 ≤ p 1) ∧
        q 0 < 2 * s 0 ∧ q 1 < 2 * s 1 := by
  have hreal : structureMap (realModule (k := k))
      ((scalingPullback s hs).monotone' hpq) ≠ 0 ↔
      0 ≤ scalingPullback s hs p 0 ∧ 0 ≤ scalingPullback s hs p 1 ∧
        (1 ≤ scalingPullback s hs p 0 ∨ 1 ≤ scalingPullback s hs p 1) ∧
        scalingPullback s hs q 0 < 2 ∧ scalingPullback s hs q 1 < 2 := by
    constructor
    · intro h
      have hactual := map_ne_zero_of_iso (realIso k)
        ((scalingPullback s hs).monotone' hpq) h
      exact (homology_structureMap_ne_zero_iff k
        ((scalingPullback s hs).monotone' hpq)).mp hactual
    · intro h
      have hactual := (homology_structureMap_ne_zero_iff k
        ((scalingPullback s hs).monotone' hpq)).mpr h
      exact map_ne_zero_of_iso (realIso k).symm
        ((scalingPullback s hs).monotone' hpq) hactual
  have hmap : structureMap (scaledHomology k s hs) hpq ≠ 0 ↔
      structureMap (realModule (k := k))
        ((scalingPullback s hs).monotone' hpq) ≠ 0 := by
    constructor
    · intro h
      have hr := map_ne_zero_of_iso (scaledRealIso k s hs).symm hpq h
      change structureMap (realModule (k := k))
        ((scalingPullback s hs).monotone' hpq) ≠ 0 at hr
      exact hr
    · intro h
      have hr : structureMap
          (reindex (scalingPullback s hs) (realModule (k := k))) hpq ≠ 0 := by
        change structureMap (realModule (k := k))
          ((scalingPullback s hs).monotone' hpq) ≠ 0
        exact h
      exact map_ne_zero_of_iso (scaledRealIso k s hs) hpq hr
  rw [hmap, hreal]
  have hnonneg0 : 0 ≤ p 0 / s 0 ↔ 0 ≤ p 0 := by
    constructor
    · intro h
      have hm : 0 ≤ (p 0 / s 0) * s 0 := mul_nonneg h (le_of_lt (hs 0))
      simpa [div_mul_cancel₀, (hs 0).ne'] using hm
    · intro h
      exact div_nonneg h (le_of_lt (hs 0))
  have hnonneg1 : 0 ≤ p 1 / s 1 ↔ 0 ≤ p 1 := by
    constructor
    · intro h
      have hm : 0 ≤ (p 1 / s 1) * s 1 := mul_nonneg h (le_of_lt (hs 1))
      simpa [div_mul_cancel₀, (hs 1).ne'] using hm
    · intro h
      exact div_nonneg h (le_of_lt (hs 1))
  have hbirth0 : 1 ≤ p 0 / s 0 ↔ s 0 ≤ p 0 := by
    rw [le_div_iff₀ (hs 0)]
    simp
  have hbirth1 : 1 ≤ p 1 / s 1 ↔ s 1 ≤ p 1 := by
    rw [le_div_iff₀ (hs 1)]
    simp
  have hdeath0 : q 0 / s 0 < 2 ↔ q 0 < 2 * s 0 := by
    rw [div_lt_iff₀ (hs 0)]
  have hdeath1 : q 1 / s 1 < 2 ↔ q 1 < 2 * s 1 := by
    rw [div_lt_iff₀ (hs 1)]
  simp only [scalingPullback_apply, hnonneg0, hnonneg1, hbirth0, hbirth1,
    hdeath0, hdeath1]

/-- The scaled birth of the arm supported from the unscaled point `(0,1)`. -/
noncomputable def scaledBirthA (s : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 0 else s 1

@[simp] theorem scaledBirthA_zero (s : Fin 2 → ℝ) : scaledBirthA s 0 = 0 := by
  simp [scaledBirthA]

@[simp] theorem scaledBirthA_one (s : Fin 2 → ℝ) : scaledBirthA s 1 = s 1 := by
  simp [scaledBirthA]

/-- The scaled birth of the arm supported from the unscaled point `(1,0)`. -/
noncomputable def scaledBirthB (s : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then s 0 else 0

@[simp] theorem scaledBirthB_zero (s : Fin 2 → ℝ) : scaledBirthB s 0 = s 0 := by
  simp [scaledBirthB]

@[simp] theorem scaledBirthB_one (s : Fin 2 → ℝ) : scaledBirthB s 1 = 0 := by
  simp [scaledBirthB]

/-- The lifetime of the first actual arm, limited by its two cap conditions. -/
noncomputable def scaledArmLifetimeA (s : Fin 2 → ℝ) : ℝ := min (2 * s 0) (s 1)

/-- The lifetime of the second actual arm, limited by its two cap conditions. -/
noncomputable def scaledArmLifetimeB (s : Fin 2 → ℝ) : ℝ := min (s 0) (2 * s 1)

/-- The sharp all-grade diagonal nilpotence threshold of the scaled PH₁ module. -/
noncomputable def scaledLifetime (s : Fin 2 → ℝ) : ℝ :=
  max (scaledArmLifetimeA s) (scaledArmLifetimeB s)

theorem scaledArmLifetimeA_pos (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    0 < scaledArmLifetimeA s := by
  unfold scaledArmLifetimeA
  exact lt_min (mul_pos (by norm_num) (hs 0)) (hs 1)

theorem scaledArmLifetimeB_pos (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    0 < scaledArmLifetimeB s := by
  unfold scaledArmLifetimeB
  exact lt_min (hs 0) (mul_pos (by norm_num) (hs 1))

theorem scaledLifetime_pos (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    0 < scaledLifetime s := by
  unfold scaledLifetime
  exact lt_max_of_lt_left (scaledArmLifetimeA_pos s hs)

private theorem structureMap_ne_zero_of_target_eq
    {k : Type u} [Field k]
    {M : PModule.{u,0,u} k (Fin 2 → ℝ)} {p q q' : Fin 2 → ℝ}
    {hpq : p ≤ q} {hpq' : p ≤ q'} (hqq' : q = q')
    (hne : structureMap M hpq ≠ 0) : structureMap M hpq' ≠ 0 := by
  cases hqq'
  exact hne

/-- The first actual scaled arm map survives exactly below its lifetime. -/
theorem scaledHomology_armA_structureMap_ne_zero_iff (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (r : ℝ) (hr0 : 0 ≤ r) :
    structureMap (scaledHomology k s hs)
      (show scaledBirthA s ≤ (fun i => scaledBirthA s i + r) from
        fun _ => le_add_of_nonneg_right hr0) ≠ 0 ↔ r < scaledArmLifetimeA s := by
  rw [scaledHomology_structureMap_ne_zero_iff]
  simp only [scaledBirthA_zero, scaledBirthA_one]
  unfold scaledArmLifetimeA
  constructor
  · rintro ⟨_, _, _, h0, h1⟩
    apply lt_min (by simpa using h0)
    linarith
  · intro hr
    rcases (lt_min_iff.mp hr) with ⟨h0, h1⟩
    refine ⟨by norm_num, (hs 1).le, Or.inr le_rfl, ?_, ?_⟩
    · simpa using h0
    · linarith

/-- The first scaled arm transition is zero at and after its endpoint. -/
theorem scaledHomology_armA_structureMap_zero_of_ge (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : scaledArmLifetimeA s ≤ r) :
    structureMap (scaledHomology k s hs)
      (show scaledBirthA s ≤ (fun i => scaledBirthA s i + r) from
        fun _ => le_add_of_nonneg_right hr0) = 0 := by
  by_contra hne
  have hlt := (scaledHomology_armA_structureMap_ne_zero_iff k s hs r hr0).mp hne
  exact (not_lt_of_ge hr) hlt

/-- The second actual scaled arm map survives exactly below its lifetime. -/
theorem scaledHomology_armB_structureMap_ne_zero_iff (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (r : ℝ) (hr0 : 0 ≤ r) :
    structureMap (scaledHomology k s hs)
      (show scaledBirthB s ≤ (fun i => scaledBirthB s i + r) from
        fun _ => le_add_of_nonneg_right hr0) ≠ 0 ↔ r < scaledArmLifetimeB s := by
  rw [scaledHomology_structureMap_ne_zero_iff]
  simp only [scaledBirthB_zero, scaledBirthB_one]
  unfold scaledArmLifetimeB
  constructor
  · rintro ⟨_, _, _, h0, h1⟩
    apply lt_min
    · linarith
    · simpa using h1
  · intro hr
    rcases (lt_min_iff.mp hr) with ⟨h0, h1⟩
    refine ⟨(hs 0).le, by norm_num, Or.inl le_rfl, ?_, ?_⟩
    · linarith
    · simpa using h1

/-- The second scaled arm transition is zero at and after its endpoint. -/
theorem scaledHomology_armB_structureMap_zero_of_ge (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : scaledArmLifetimeB s ≤ r) :
    structureMap (scaledHomology k s hs)
      (show scaledBirthB s ≤ (fun i => scaledBirthB s i + r) from
        fun _ => le_add_of_nonneg_right hr0) = 0 := by
  by_contra hne
  have hlt := (scaledHomology_armB_structureMap_ne_zero_iff k s hs r hr0).mp hne
  exact (not_lt_of_ge hr) hlt

/-- Both actual scaled arm birth fibers are nonzero. -/
theorem scaledHomology_birthA_not_isZero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    ¬ IsZero ((scaledHomology k s hs).obj (scaledBirthA s)) := by
  intro hz
  have hmap := (scaledHomology_armA_structureMap_ne_zero_iff k s hs 0 (by norm_num)).2
    (scaledArmLifetimeA_pos s hs)
  exact hmap (hz.eq_of_src _ _)

theorem scaledHomology_birthB_not_isZero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    ¬ IsZero ((scaledHomology k s hs).obj (scaledBirthB s)) := by
  intro hz
  have hmap := (scaledHomology_armB_structureMap_ne_zero_iff k s hs 0 (by norm_num)).2
    (scaledArmLifetimeB_pos s hs)
  exact hmap (hz.eq_of_src _ _)

/-- Every actual PH₁ structure map across the sharp diagonal lifetime threshold
vanishes, at every real source grade. -/
theorem scaledHomology_lifetime_structureMap_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (r : ℝ)
    (hr : scaledLifetime s ≤ r) (p : Fin 2 → ℝ) :
    structureMap (scaledHomology k s hs)
      (show p ≤ (fun i => p i + r) from
        fun _ => le_add_of_nonneg_right ((scaledLifetime_pos s hs).le.trans hr)) = 0 := by
  by_contra hne
  have hchar := (scaledHomology_structureMap_ne_zero_iff k s hs
    (show p ≤ (fun i => p i + r) from
      fun _ => le_add_of_nonneg_right ((scaledLifetime_pos s hs).le.trans hr))).mp hne
  rcases hchar with ⟨hp0, hp1, harms, hq0, hq1⟩
  change p 0 + r < 2 * s 0 at hq0
  change p 1 + r < 2 * s 1 at hq1
  rcases harms with hb | ha
  · have hLifeB : scaledArmLifetimeB s ≤ r :=
      (le_trans (le_max_right (scaledArmLifetimeA s) (scaledArmLifetimeB s)) hr)
    have hminB : min (s 0) (2 * s 1) ≤ r := by
      change scaledArmLifetimeB s ≤ r at hLifeB
      exact hLifeB
    rcases min_le_iff.mp hminB with h0 | h1
    · linarith
    · linarith
  · have hLifeA : scaledArmLifetimeA s ≤ r :=
      (le_trans (le_max_left (scaledArmLifetimeA s) (scaledArmLifetimeB s)) hr)
    have hminA : min (2 * s 0) (s 1) ≤ r := by
      change scaledArmLifetimeA s ≤ r at hLifeA
      exact hLifeA
    rcases min_le_iff.mp hminA with h0 | h1
    · linarith
    · linarith

private theorem scaledHomology_map_zero_of_step (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (r : ℝ)
    (hr : scaledLifetime s ≤ r) {p q : Fin 2 → ℝ} (hpq : p ≤ q)
    (hstep : ∀ i, q i = p i + r) : structureMap (scaledHomology k s hs) hpq = 0 := by
  have hq : q = fun i => p i + r := funext hstep
  subst q
  exact scaledHomology_lifetime_structureMap_zero k s hs r hr p

private theorem scaledOptimalRadius_double (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    scaledLifetime s ≤ 2 * ((Real.toNNReal (scaledLifetime s / 2) : ℝ)) := by
  rw [Real.coe_toNNReal _ (div_nonneg (scaledLifetime_pos s hs).le (by norm_num))]
  nlinarith

/-- An explicit optimal interleaving with the categorical zero PH₁ module.
Both natural transformations are zero. The scaled-module equation uses vanishing
of its T-transition; the zero-module equation follows from the zero object. -/
noncomputable def scaledHomologyZeroInterleaving (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    CoordinateInterleaving (Real.toNNReal (scaledLifetime s / 2))
      (scaledHomology k s hs) (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := by
  let ε : ℝ≥0 := Real.toNNReal (scaledLifetime s / 2)
  have hT : scaledLifetime s ≤ 2 * (ε : ℝ) := scaledOptimalRadius_double s hs
  refine CoordinateInterleaving.ofStructureMapEquations 0 0 ?_ ?_
  · intro p
    change (0 : (scaledHomology k s hs).obj p ⟶
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)).obj (CoordinateShift.translation ε p)) ≫ 0 = _
    rw [zero_comp]
    symm
    apply scaledHomology_map_zero_of_step k s hs (2 * (ε : ℝ)) hT
    intro i
    simp only [CoordinateShift.translation_apply]
    ring
  · intro p
    change (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)).obj p ⟶
      (scaledHomology k s hs).obj (CoordinateShift.translation ε p)) ≫ 0 = _
    rw [zero_comp]
    symm
    exact (Functor.zero_obj p).eq_of_src _ _

@[simp] theorem scaledHomologyZeroInterleaving_φ (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    (scaledHomologyZeroInterleaving k s hs).φ = 0 := rfl

@[simp] theorem scaledHomologyZeroInterleaving_ψ (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    (scaledHomologyZeroInterleaving k s hs).ψ = 0 := rfl

/-- Any radius strictly below half the sharp lifetime is obstructed by an
actual surviving arm map and the interleaving equation through the zero module. -/
theorem scaledHomology_no_zero_interleaving (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (ε : ℝ≥0)
    (hε : (ε : ℝ) < scaledLifetime s / 2) :
    IsEmpty (CoordinateInterleaving ε (scaledHomology k s hs)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) := by
  refine ⟨fun I => ?_⟩
  have hr0 : 0 ≤ 2 * (ε : ℝ) := by positivity
  have hrT : 2 * (ε : ℝ) < scaledLifetime s := by linarith
  rcases le_total (scaledArmLifetimeA s) (scaledArmLifetimeB s) with hAB | hBA
  · let p := scaledBirthB s
    have hrB : 2 * (ε : ℝ) < scaledArmLifetimeB s := by
      have h := hrT
      rw [scaledLifetime, max_eq_right hAB] at h
      exact h
    have hmap := (scaledHomology_armB_structureMap_ne_zero_iff k s hs
      (2 * (ε : ℝ)) hr0).2 hrB
    have htarget : (fun i => p i + 2 * (ε : ℝ)) =
        CoordinateShift.translation ε (CoordinateShift.translation ε p) := by
      funext i
      simp only [CoordinateShift.translation_apply]
      ring
    have hsurvive := structureMap_ne_zero_of_target_eq
      (M := scaledHomology k s hs) (p := p)
      (q := fun i => p i + 2 * (ε : ℝ))
      (q' := CoordinateShift.translation ε (CoordinateShift.translation ε p))
      (hpq := fun _ => le_add_of_nonneg_right hr0)
      (hpq' := CoordinateInterleaving.twice_le ε p) htarget hmap
    have hzero : IsZero ((0 : PModule.{u,0,u} k (Fin 2 → ℝ)).obj
        (CoordinateShift.translation ε p)) := Functor.zero_obj _
    have hf : I.φ.app p = 0 := hzero.eq_of_tgt _ _
    exact hsurvive (by erw [← I.φ_ψ_structureMap p, hf, zero_comp])
  · let p := scaledBirthA s
    have hrA : 2 * (ε : ℝ) < scaledArmLifetimeA s := by
      have h := hrT
      rw [scaledLifetime, max_eq_left hBA] at h
      exact h
    have hmap := (scaledHomology_armA_structureMap_ne_zero_iff k s hs
      (2 * (ε : ℝ)) hr0).2 hrA
    have htarget : (fun i => p i + 2 * (ε : ℝ)) =
        CoordinateShift.translation ε (CoordinateShift.translation ε p) := by
      funext i
      simp only [CoordinateShift.translation_apply]
      ring
    have hsurvive := structureMap_ne_zero_of_target_eq
      (M := scaledHomology k s hs) (p := p)
      (q := fun i => p i + 2 * (ε : ℝ))
      (q' := CoordinateShift.translation ε (CoordinateShift.translation ε p))
      (hpq := fun _ => le_add_of_nonneg_right hr0)
      (hpq' := CoordinateInterleaving.twice_le ε p) htarget hmap
    have hzero : IsZero ((0 : PModule.{u,0,u} k (Fin 2 → ℝ)).obj
        (CoordinateShift.translation ε p)) := Functor.zero_obj _
    have hf : I.φ.app p = 0 := hzero.eq_of_tgt _ _
    exact hsurvive (by erw [← I.φ_ψ_structureMap p, hf, zero_comp])

private theorem scaledOptimalRadius_coe (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    ((Real.toNNReal (scaledLifetime s / 2) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (scaledLifetime s / 2) := by
  rw [ENNReal.coe_nnreal_eq]
  have hnonneg : 0 ≤ scaledLifetime s / 2 :=
    div_nonneg (scaledLifetime_pos s hs).le (by norm_num)
  rw [Real.coe_toNNReal _ hnonneg]

private theorem scaledHomology_distance_lower (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    ENNReal.ofReal (scaledLifetime s / 2) ≤
      coordinateInterleavingDistance (scaledHomology k s hs)
        (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := by
  apply le_coordinateInterleavingDistance_iff.mpr
  rintro ε ⟨I⟩
  have hrad : scaledLifetime s / 2 ≤ (ε : ℝ) := by
    by_contra h
    exact (scaledHomology_no_zero_interleaving k s hs ε (lt_of_not_ge h)).false I
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hrad

/-- Exact interleaving distance from the actual scaled PH₁ module to zero. -/
theorem coordinateInterleavingDistance_scaledHomology_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    coordinateInterleavingDistance (scaledHomology k s hs)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) =
        ENNReal.ofReal (scaledLifetime s / 2) := by
  apply le_antisymm
  · calc
      coordinateInterleavingDistance (scaledHomology k s hs)
          (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ≤
            ((Real.toNNReal (scaledLifetime s / 2) : ℝ≥0) : ℝ≥0∞) :=
              (scaledHomologyZeroInterleaving k s hs).distance_le
      _ = ENNReal.ofReal (scaledLifetime s / 2) := scaledOptimalRadius_coe s hs
  · exact scaledHomology_distance_lower k s hs

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
