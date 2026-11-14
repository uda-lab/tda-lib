import TDA.Persistence.RankResolutionDegreeTwoSimplicialScaling

/-!
# Uniform translates after positive coordinate scaling

This file studies the actual degree-one persistence module of the face grading
obtained by first positively scaling both coordinates and then adding a common
signed delay.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory CategoryTheory.Limits TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal ZeroObject

/-- Undo the common signed delay, then pull back through positive scaling. -/
noncomputable def scaledTranslatedPullback (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t : ℝ) : (Fin 2 → ℝ) →o (Fin 2 → ℝ) :=
  (scalingPullback s hs).comp (translationPullback t)

@[simp] theorem scaledTranslatedPullback_apply (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t : ℝ) (p : Fin 2 → ℝ) (i : Fin 2) :
    scaledTranslatedPullback s hs t p i = (p i - t) / s i := by
  simp [scaledTranslatedPullback]

/-- Add a uniform signed delay after scaling each face-grade coordinate. -/
def scaledTranslatedGrading (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) :
    FiniteGraded boundaryTetrahedron 2 where
  grade σ i := s i * boundaryTetrahedronGrading.grade σ i + t
  mono h i := by
    have hg := boundaryTetrahedronGrading.mono h i
    simpa [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hg (le_of_lt (hs i))) t

@[simp] theorem scaledTranslatedGrading_grade (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t : ℝ) (σ : TotalFace boundaryTetrahedron.toPre)
    (i : Fin 2) :
    (scaledTranslatedGrading s hs t).grade σ i =
      s i * boundaryTetrahedronGrading.grade σ i + t := rfl

/-- Zero delay recovers the already established positive scaling input. -/
theorem scaledTranslatedGrading_zero (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    scaledTranslatedGrading s hs 0 = scaledGrading s hs := by
  apply FiniteGraded.ext
  intro σ
  funext i
  simp [scaledTranslatedGrading, scaledGrading]

/-- Unit scaling recovers the established scalar-translation input. -/
theorem scaledTranslatedGrading_one (t : ℝ) :
    scaledTranslatedGrading (fun _ : Fin 2 => (1 : ℝ)) (fun _ => by norm_num) t =
      translatedGrading t := by
  apply FiniteGraded.ext
  intro σ
  funext i
  simp [scaledTranslatedGrading, translatedGrading]

/-- The sublevel filtration is the original one at `(p-t)/s`. -/
theorem scaledTranslatedGrading_sublevel (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t : ℝ) (p : Fin 2 → ℝ) :
    (scaledTranslatedGrading s hs t).sublevel p =
      boundaryTetrahedronGrading.sublevel (scaledTranslatedPullback s hs t p) := by
  apply le_antisymm
  · rintro σ ⟨hσ, hp⟩
    refine ⟨hσ, fun i => ?_⟩
    change boundaryTetrahedronGrading.grade ⟨σ, hσ⟩ i ≤ (p i - t) / s i
    apply (le_div_iff₀ (hs i)).2
    have hi := hp i
    change s i * boundaryTetrahedronGrading.grade ⟨σ, hσ⟩ i + t ≤ p i at hi
    linarith
  · rintro σ ⟨hσ, hp⟩
    refine ⟨hσ, fun i => ?_⟩
    change s i * boundaryTetrahedronGrading.grade ⟨σ, hσ⟩ i + t ≤ p i
    have hi : boundaryTetrahedronGrading.grade ⟨σ, hσ⟩ i ≤ (p i - t) / s i := hp i
    have hi' := (le_div_iff₀ (hs i)).1 hi
    linarith

/-- The translated sublevel filtration is the scaled one at index `p-t`. -/
theorem scaledTranslatedGrading_scaledSublevel (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t : ℝ) (p : Fin 2 → ℝ) :
    (scaledTranslatedGrading s hs t).sublevel p =
      (scaledGrading s hs).sublevel (translationPullback t p) := by
  rw [scaledTranslatedGrading_sublevel, scaledGrading_sublevel]
  congr 1

/-- The actual PH₁ persistence module of the translated, scaled face filtration. -/
noncomputable abbrev scaledTranslatedHomology (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) :
    PModule.{u,0,u} k (Fin 2 → ℝ) :=
  finiteSimplicialHomology k (scaledTranslatedGrading s hs t) 1

/-- Zero delay recovers the actual positive-scaling PH₁ module. -/
theorem scaledTranslatedHomology_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    scaledTranslatedHomology k s hs 0 = scaledHomology k s hs := by
  simp only [scaledTranslatedHomology, scaledTranslatedGrading_zero, scaledHomology]

/-- Translation of the scaled input is the actual scaled module reindexed by `p-t`. -/
noncomputable def scaledTranslatedHomologyScaledReindexIso (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) :
    scaledTranslatedHomology k s hs t ≅
      reindex (translationPullback t) (scaledHomology k s hs) := by
  have hfil : (scaledTranslatedGrading s hs t).sublevelFiltration =
      TDA.Filtration.reindex (translationPullback t) (scaledGrading s hs).sublevelFiltration := by
    apply DFunLike.ext
    intro p
    exact scaledTranslatedGrading_scaledSublevel s hs t p
  unfold scaledTranslatedHomology finiteSimplicialHomology scaledHomology
  rw [hfil]
  exact Iso.refl _

/-- Unit scale recovers the established actual scalar-translation module. -/
theorem scaledTranslatedHomology_one (k : Type u) [Field k] (t : ℝ) :
    scaledTranslatedHomology k (fun _ : Fin 2 => (1 : ℝ)) (fun _ => by norm_num) t =
      translatedHomology k t := by
  simp only [scaledTranslatedHomology, scaledTranslatedGrading_one, translatedHomology]

/-- The actual module is naturally reindexed from the original actual PH₁ module. -/
noncomputable def scaledTranslatedHomologyReindexIso (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) :
    scaledTranslatedHomology k s hs t ≅
      reindex (scaledTranslatedPullback s hs t)
        (finiteSimplicialHomology k boundaryTetrahedronGrading 1) := by
  have hfil : (scaledTranslatedGrading s hs t).sublevelFiltration =
      TDA.Filtration.reindex (scaledTranslatedPullback s hs t)
        boundaryTetrahedronGrading.sublevelFiltration := by
    apply DFunLike.ext
    intro p
    exact scaledTranslatedGrading_sublevel s hs t p
  unfold scaledTranslatedHomology finiteSimplicialHomology
  rw [hfil]
  exact Iso.refl _

/-- Realization in the original actual Lan, with pullback `(p-t)/s`. -/
noncomputable def scaledTranslatedRealIso (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) :
    scaledTranslatedHomology k s hs t ≅
      reindex (scaledTranslatedPullback s hs t) (realModule (k := k)) :=
  (scaledTranslatedHomologyReindexIso k s hs t).trans
    (Functor.isoWhiskerLeft (scaledTranslatedPullback s hs t).toFunctor (realIso k))

/-- Naturality on every actual inclusion-induced PH₁ structure map. -/
theorem scaledTranslatedRealIso_structureMap (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (scaledTranslatedHomology k s hs t) hpq ≫
        (scaledTranslatedRealIso k s hs t).hom.app q =
      (scaledTranslatedRealIso k s hs t).hom.app p ≫
        structureMap (realModule (k := k))
          ((scaledTranslatedPullback s hs t).monotone' hpq) :=
  (scaledTranslatedRealIso k s hs t).hom.naturality (homOfLE hpq)

/-- Finite presentation follows from the literal finite simplicial input. -/
theorem scaledTranslatedHomology_finitelyPresented (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (scaledTranslatedHomology k s hs t) :=
  finiteSimplicialHomology_finitelyPresented k (scaledTranslatedGrading s hs t) 1

private theorem scaledTranslated_map_ne_zero_of_iso {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} (e : M ≅ N)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) (hne : structureMap N hpq ≠ 0) :
    structureMap M hpq ≠ 0 := by
  intro hz
  apply hne
  apply (cancel_mono (e.symm.hom.app q)).mp
  have hn := e.symm.hom.naturality (homOfLE hpq)
  change structureMap N hpq ≫ e.symm.hom.app q =
    e.symm.hom.app p ≫ structureMap M hpq at hn
  rw [hn, hz, comp_zero, zero_comp]

private theorem scaledTranslated_map_zero_of_iso {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} (e : M ≅ N)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) (hz : structureMap N hpq = 0) :
    structureMap M hpq = 0 := by
  apply (cancel_mono (e.hom.app q)).mp
  have hn := e.hom.naturality (homOfLE hpq)
  change structureMap M hpq ≫ e.hom.app q = e.hom.app p ≫ structureMap N hpq at hn
  rw [hn, hz, comp_zero, zero_comp]

private theorem scaledTranslated_map_ne_zero_of_index_eq {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} {p p' q q' : Fin 2 → ℝ}
    (hM : M = N) (hp : p = p') (hq : q = q')
    {h : p ≤ q} {h' : p' ≤ q'} (hne : structureMap N h' ≠ 0) :
    structureMap M h ≠ 0 := by
  cases hM
  cases hp
  cases hq
  exact hne

private theorem scaledTranslated_map_zero_of_index_eq {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} {p p' q q' : Fin 2 → ℝ}
    (hM : M = N) (hp : p = p') (hq : q = q')
    {h : p ≤ q} {h' : p' ≤ q'} (hz : structureMap N h' = 0) :
    structureMap M h = 0 := by
  cases hM
  cases hp
  cases hq
  exact hz

private theorem scaledTranslated_map_zero_of_target_eq {k : Type u} [Field k]
    {M : PModule.{u,0,u} k (Fin 2 → ℝ)} {p q q' : Fin 2 → ℝ}
    (hqq' : q = q') {hpq : p ≤ q} {hpq' : p ≤ q'}
    (hz : structureMap M hpq = 0) : structureMap M hpq' = 0 := by
  cases hqq'
  exact hz

private theorem scaledTranslated_map_ne_zero_of_target_eq {k : Type u} [Field k]
    {M : PModule.{u,0,u} k (Fin 2 → ℝ)} {p q q' : Fin 2 → ℝ}
    (hqq' : q = q') {hpq : p ≤ q} {hpq' : p ≤ q'}
    (hne : structureMap M hpq ≠ 0) : structureMap M hpq' ≠ 0 := by
  cases hqq'
  exact hne

/-- Characteristic of every actual structure map of the translated PH₁ module. -/
theorem scaledTranslatedHomology_structureMap_ne_zero_iff (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (scaledTranslatedHomology k s hs t) hpq ≠ 0 ↔
      0 ≤ p 0 - t ∧ 0 ≤ p 1 - t ∧
        (s 0 ≤ p 0 - t ∨ s 1 ≤ p 1 - t) ∧
        q 0 - t < 2 * s 0 ∧ q 1 - t < 2 * s 1 := by
  have hmap : structureMap (scaledTranslatedHomology k s hs t) hpq ≠ 0 ↔
      structureMap (scaledHomology k s hs)
        ((translationPullback t).monotone' hpq) ≠ 0 := by
    constructor
    · intro h
      have hr := scaledTranslated_map_ne_zero_of_iso
        (scaledTranslatedHomologyScaledReindexIso k s hs t).symm hpq h
      change structureMap (reindex (translationPullback t) (scaledHomology k s hs))
        hpq ≠ 0 at hr
      simpa only [structureMap_reindex] using hr
    · intro h
      have hr : structureMap (reindex (translationPullback t)
          (scaledHomology k s hs)) hpq ≠ 0 := by
        simpa only [structureMap_reindex] using h
      exact scaledTranslated_map_ne_zero_of_iso
        (scaledTranslatedHomologyScaledReindexIso k s hs t) hpq hr
  rw [hmap, scaledHomology_structureMap_ne_zero_iff]
  change (0 ≤ translationPullback t p 0 ∧ 0 ≤ translationPullback t p 1 ∧
      (s 0 ≤ translationPullback t p 0 ∨ s 1 ≤ translationPullback t p 1) ∧
      translationPullback t q 0 < 2 * s 0 ∧ translationPullback t q 1 < 2 * s 1) ↔ _
  simpa only [translationPullback_apply]

/-- Below either shifted coordinate birth, the actual PH₁ fiber is zero. -/
theorem scaledTranslatedHomology_isZero_of_coordinate_lt (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t : ℝ) (p : Fin 2 → ℝ)
    (i : Fin 2) (hp : p i < t) :
    IsZero ((scaledTranslatedHomology k s hs t).obj p) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have hid : structureMap (scaledTranslatedHomology k s hs t) (le_rfl : p ≤ p) = 0 := by
    by_contra hne
    have hchar := (scaledTranslatedHomology_structureMap_ne_zero_iff k s hs t
      (le_rfl : p ≤ p)).mp hne
    fin_cases i
    · change p 0 < t at hp
      have hneg : p 0 - t < 0 := by linarith
      exact (not_le_of_gt hneg) hchar.1
    · change p 1 < t at hp
      have hneg : p 1 - t < 0 := by linarith
      exact (not_le_of_gt hneg) hchar.2.1
  simpa only [structureMap_self] using hid

/-- The arm beginning on coordinate zero's opposite side after uniform delay. -/
noncomputable def scaledTranslatedBirthA (s : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  fun i => scaledBirthA s i + t

/-- The arm beginning on coordinate one's opposite side after uniform delay. -/
noncomputable def scaledTranslatedBirthB (s : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  fun i => scaledBirthB s i + t

@[simp] theorem scaledTranslatedBirthA_zero (s : Fin 2 → ℝ) (t : ℝ) :
    scaledTranslatedBirthA s t 0 = t := by simp [scaledTranslatedBirthA]

@[simp] theorem scaledTranslatedBirthB_one (s : Fin 2 → ℝ) (t : ℝ) :
    scaledTranslatedBirthB s t 1 = t := by simp [scaledTranslatedBirthB]

private theorem scaledTranslatedPullback_birthA (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t : ℝ) :
    translationPullback t (scaledTranslatedBirthA s t) = scaledBirthA s := by
  funext i
  simp [scaledTranslatedBirthA, translationPullback_apply]

private theorem scaledTranslatedPullback_birthB (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t : ℝ) :
    translationPullback t (scaledTranslatedBirthB s t) = scaledBirthB s := by
  funext i
  simp [scaledTranslatedBirthB, translationPullback_apply]

private theorem scaledTranslatedPullback_birthA_step (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t r : ℝ) :
    translationPullback t (fun i => scaledTranslatedBirthA s t i + r) =
      fun i => scaledBirthA s i + r := by
  funext i
  simp only [translationPullback_apply, scaledTranslatedBirthA]
  ring

private theorem scaledTranslatedPullback_birthB_step (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t r : ℝ) :
    translationPullback t (fun i => scaledTranslatedBirthB s t i + r) =
      fun i => scaledBirthB s i + r := by
  funext i
  simp only [translationPullback_apply, scaledTranslatedBirthB]
  ring

/-- The actual A-arm structure map survives exactly below its scaled lifetime. -/
theorem scaledTranslatedHomology_armA_structureMap_ne_zero_iff (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t r : ℝ) (hr0 : 0 ≤ r) :
    structureMap (scaledTranslatedHomology k s hs t)
      (show scaledTranslatedBirthA s t ≤
        (fun i => scaledTranslatedBirthA s t i + r) from
          fun _ => le_add_of_nonneg_right hr0) ≠ 0 ↔ r < scaledArmLifetimeA s := by
  rw [scaledTranslatedHomology_structureMap_ne_zero_iff]
  have hs0 : scaledTranslatedBirthA s t 0 - t = 0 := by
    simp [scaledTranslatedBirthA, scaledBirthA]
  have hs1 : scaledTranslatedBirthA s t 1 - t = s 1 := by
    simp [scaledTranslatedBirthA, scaledBirthA]
  have ht0 : (scaledTranslatedBirthA s t 0 + r) - t = r := by
    calc
      (scaledTranslatedBirthA s t 0 + r) - t =
          (scaledTranslatedBirthA s t 0 - t) + r := by ring
      _ = r := by rw [hs0]; ring
  have ht1 : (scaledTranslatedBirthA s t 1 + r) - t = s 1 + r := by
    calc
      (scaledTranslatedBirthA s t 1 + r) - t =
          (scaledTranslatedBirthA s t 1 - t) + r := by ring
      _ = s 1 + r := by rw [hs1]
  simp only [hs0, hs1, ht0, ht1]
  change (0 ≤ 0 ∧ 0 ≤ s 1 ∧ (s 0 ≤ 0 ∨ s 1 ≤ s 1) ∧
      r < 2 * s 0 ∧ s 1 + r < 2 * s 1) ↔ r < min (2 * s 0) (s 1)
  constructor
  · rintro ⟨h0, h1, harms, hq0, hq1⟩
    rw [lt_min_iff]
    exact ⟨hq0, by linarith⟩
  · intro hr
    rcases lt_min_iff.mp hr with ⟨h0, h1⟩
    exact ⟨le_rfl, (hs 1).le, Or.inr le_rfl, h0, by linarith⟩

/-- The actual B-arm structure map survives exactly below its scaled lifetime. -/
theorem scaledTranslatedHomology_armB_structureMap_ne_zero_iff (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t r : ℝ) (hr0 : 0 ≤ r) :
    structureMap (scaledTranslatedHomology k s hs t)
      (show scaledTranslatedBirthB s t ≤
        (fun i => scaledTranslatedBirthB s t i + r) from
          fun _ => le_add_of_nonneg_right hr0) ≠ 0 ↔ r < scaledArmLifetimeB s := by
  rw [scaledTranslatedHomology_structureMap_ne_zero_iff]
  have hs0 : scaledTranslatedBirthB s t 0 - t = s 0 := by
    simp [scaledTranslatedBirthB, scaledBirthB]
  have hs1 : scaledTranslatedBirthB s t 1 - t = 0 := by
    simp [scaledTranslatedBirthB, scaledBirthB]
  have ht0 : (scaledTranslatedBirthB s t 0 + r) - t = s 0 + r := by
    calc
      (scaledTranslatedBirthB s t 0 + r) - t =
          (scaledTranslatedBirthB s t 0 - t) + r := by ring
      _ = s 0 + r := by rw [hs0]
  have ht1 : (scaledTranslatedBirthB s t 1 + r) - t = r := by
    calc
      (scaledTranslatedBirthB s t 1 + r) - t =
          (scaledTranslatedBirthB s t 1 - t) + r := by ring
      _ = r := by rw [hs1]; ring
  simp only [hs0, hs1, ht0, ht1]
  change (0 ≤ s 0 ∧ 0 ≤ 0 ∧ (s 0 ≤ s 0 ∨ s 1 ≤ 0) ∧
      s 0 + r < 2 * s 0 ∧ r < 2 * s 1) ↔ r < min (s 0) (2 * s 1)
  constructor
  · rintro ⟨_, _, _, hq0, hq1⟩
    rw [lt_min_iff]
    exact ⟨by linarith, hq1⟩
  · intro hr
    rcases lt_min_iff.mp hr with ⟨h0, h1⟩
    exact ⟨(hs 0).le, le_rfl, Or.inl le_rfl, by linarith, h1⟩

/-- Every translated actual PH₁ map across the full diagonal lifetime is zero. -/
theorem scaledTranslatedHomology_lifetime_structureMap_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t r : ℝ)
    (hr : scaledLifetime s ≤ r) (p : Fin 2 → ℝ) :
    structureMap (scaledTranslatedHomology k s hs t)
      (show p ≤ (fun i => p i + r) from
        fun _ => le_add_of_nonneg_right ((scaledLifetime_pos s hs).le.trans hr)) = 0 := by
  let hpq : p ≤ fun i => p i + r := fun _ => le_add_of_nonneg_right
    ((scaledLifetime_pos s hs).le.trans hr)
  apply scaledTranslated_map_zero_of_iso
    (scaledTranslatedHomologyScaledReindexIso k s hs t) hpq
  rw [structureMap_reindex]
  have htarget : translationPullback t (fun i => p i + r) =
      fun i => translationPullback t p i + r := by
    funext i
    simp only [translationPullback_apply]
    ring
  exact scaledTranslated_map_zero_of_index_eq rfl rfl htarget
    (scaledHomology_lifetime_structureMap_zero k s hs r hr (translationPullback t p))

/-- Actual grade differences give a magnitude interleaving of the translated modules. -/
theorem scaledTranslatedGrading_grade_error (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t u : ℝ) :
    ∀ σ i, |(scaledTranslatedGrading s hs t).grade σ i -
      (scaledTranslatedGrading s hs u).grade σ i| ≤ (Real.toNNReal |t - u| : ℝ) := by
  have hδ : ((Real.toNNReal |t - u| : ℝ≥0) : ℝ) = |t - u| :=
    Real.coe_toNNReal _ (abs_nonneg _)
  intro σ i
  rw [scaledTranslatedGrading_grade, scaledTranslatedGrading_grade, hδ]
  apply le_of_eq
  congr 1
  ring

/-- Actual grade differences give a magnitude interleaving of the translated modules. -/
noncomputable def scaledTranslatedHomologyMagnitudeInterleaving (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    CoordinateInterleaving (Real.toNNReal |t - u|)
      (scaledTranslatedHomology k s hs t) (scaledTranslatedHomology k s hs u) := by
  exact finiteSimplicialHomology_interleaving k
    (scaledTranslatedGrading s hs t) (scaledTranslatedGrading s hs u) 1
    (scaledTranslatedGrading_grade_error s hs t u)

/-- The forward magnitude witness map is the actual simplicial inclusion map. -/
@[simp] theorem scaledTranslatedHomologyMagnitudeInterleaving_φ_app
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ)
    (p : Fin 2 → ℝ) :
    (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).φ.app p =
      simplicialHomologyIncl k
        ((scaledTranslatedGrading s hs t).sublevel_le_translation_of_error
          (scaledTranslatedGrading s hs u) (scaledTranslatedGrading_grade_error s hs t u) p) 1 :=
  finiteSimplicialHomology_interleaving_φ_app k (scaledTranslatedGrading s hs t)
    (scaledTranslatedGrading s hs u) 1 (scaledTranslatedGrading_grade_error s hs t u) p

/-- The reverse magnitude witness map is the actual simplicial inclusion map. -/
@[simp] theorem scaledTranslatedHomologyMagnitudeInterleaving_ψ_app
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ)
    (p : Fin 2 → ℝ) :
    (scaledTranslatedHomologyMagnitudeInterleaving k s hs t u).ψ.app p =
      simplicialHomologyIncl k
        ((scaledTranslatedGrading s hs u).sublevel_le_translation_of_error
          (scaledTranslatedGrading s hs t)
          (fun σ i => by
            simpa only [abs_sub_comm] using scaledTranslatedGrading_grade_error s hs t u σ i) p) 1 :=
  finiteSimplicialHomology_interleaving_ψ_app k (scaledTranslatedGrading s hs t)
    (scaledTranslatedGrading s hs u) 1 (scaledTranslatedGrading_grade_error s hs t u) p

private theorem scaledTranslatedLifetimeRadius_double (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) :
    scaledLifetime s ≤ 2 * ((Real.toNNReal (scaledLifetime s / 2) : ℝ)) := by
  rw [Real.coe_toNNReal _ (div_nonneg (scaledLifetime_pos s hs).le (by norm_num))]
  nlinarith

/-- An interleaving with both cross transformations zero at the half-lifetime radius.
Both equations use their actual vanishing full-lifetime structure maps. -/
noncomputable def scaledTranslatedHomologyLifetimeInterleaving (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    CoordinateInterleaving (Real.toNNReal (scaledLifetime s / 2))
      (scaledTranslatedHomology k s hs t) (scaledTranslatedHomology k s hs u) := by
  let ε : ℝ≥0 := Real.toNNReal (scaledLifetime s / 2)
  have hT : scaledLifetime s ≤ 2 * (ε : ℝ) := scaledTranslatedLifetimeRadius_double s hs
  refine CoordinateInterleaving.ofStructureMapEquations 0 0 ?_ ?_
  · intro p
    change (0 : (scaledTranslatedHomology k s hs t).obj p ⟶
      (scaledTranslatedHomology k s hs u).obj (CoordinateShift.translation ε p)) ≫ 0 = _
    rw [zero_comp]
    symm
    have hzero := scaledTranslatedHomology_lifetime_structureMap_zero k s hs t
      (2 * (ε : ℝ)) hT p
    have htarget : (fun i => p i + 2 * (ε : ℝ)) =
        CoordinateShift.translation ε (CoordinateShift.translation ε p) := by
      funext i
      simp only [CoordinateShift.translation_apply]
      ring
    exact scaledTranslated_map_zero_of_target_eq htarget hzero
  · intro p
    change (0 : (scaledTranslatedHomology k s hs u).obj p ⟶
      (scaledTranslatedHomology k s hs t).obj (CoordinateShift.translation ε p)) ≫ 0 = _
    rw [zero_comp]
    symm
    have hzero := scaledTranslatedHomology_lifetime_structureMap_zero k s hs u
      (2 * (ε : ℝ)) hT p
    have htarget : (fun i => p i + 2 * (ε : ℝ)) =
        CoordinateShift.translation ε (CoordinateShift.translation ε p) := by
      funext i
      simp only [CoordinateShift.translation_apply]
      ring
    exact scaledTranslated_map_zero_of_target_eq htarget hzero

@[simp] theorem scaledTranslatedHomologyLifetimeInterleaving_φ
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    (scaledTranslatedHomologyLifetimeInterleaving k s hs t u).φ = 0 := rfl

@[simp] theorem scaledTranslatedHomologyLifetimeInterleaving_ψ
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    (scaledTranslatedHomologyLifetimeInterleaving k s hs t u).ψ = 0 := rfl

private theorem scaledTranslatedHomology_no_interleaving_ordered (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) (ε : ℝ≥0)
    (htu : t ≤ u) (hgap : (ε : ℝ) < |t - u|)
    (hlife : (ε : ℝ) < scaledLifetime s / 2) :
    IsEmpty (CoordinateInterleaving ε (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u)) := by
  refine ⟨fun I => ?_⟩
  have hgap' : (ε : ℝ) < u - t := by
    rw [abs_of_nonpos (sub_nonpos.mpr htu)] at hgap
    linarith
  have hmiddle : t + (ε : ℝ) < u := by linarith
  have h2ε : 0 ≤ 2 * (ε : ℝ) := by positivity
  have h2T : 2 * (ε : ℝ) < scaledLifetime s := by linarith
  rcases le_total (scaledArmLifetimeA s) (scaledArmLifetimeB s) with hAB | hBA
  · let p := scaledTranslatedBirthB s t
    have hlifeB : 2 * (ε : ℝ) < scaledArmLifetimeB s := by
      rw [scaledLifetime, max_eq_right hAB] at h2T
      exact h2T
    have hmap := (scaledTranslatedHomology_armB_structureMap_ne_zero_iff k s hs t
      (2 * (ε : ℝ)) h2ε).2 hlifeB
    have htarget : (fun i => p i + 2 * (ε : ℝ)) =
        CoordinateShift.translation ε (CoordinateShift.translation ε p) := by
      funext i
      simp only [CoordinateShift.translation_apply]
      ring
    have hsurvive := scaledTranslated_map_ne_zero_of_target_eq
      (M := scaledTranslatedHomology k s hs t) (p := p)
      (q := fun i => p i + 2 * (ε : ℝ))
      (q' := CoordinateShift.translation ε (CoordinateShift.translation ε p))
      (hpq' := CoordinateInterleaving.twice_le ε p)
      htarget hmap
    have hcoord : (CoordinateShift.translation ε p) 1 < u := by
      simpa [CoordinateShift.translation_apply, p, scaledTranslatedBirthB] using hmiddle
    have hzero : IsZero ((scaledTranslatedHomology k s hs u).obj
        (CoordinateShift.translation ε p)) :=
      scaledTranslatedHomology_isZero_of_coordinate_lt k s hs u _ 1 hcoord
    have hφ : I.φ.app p = 0 := hzero.eq_of_tgt _ _
    have heq := I.φ_ψ_structureMap p
    rw [hφ, zero_comp] at heq
    exact hsurvive heq.symm
  · let p := scaledTranslatedBirthA s t
    have hlifeA : 2 * (ε : ℝ) < scaledArmLifetimeA s := by
      rw [scaledLifetime, max_eq_left hBA] at h2T
      exact h2T
    have hmap := (scaledTranslatedHomology_armA_structureMap_ne_zero_iff k s hs t
      (2 * (ε : ℝ)) h2ε).2 hlifeA
    have htarget : (fun i => p i + 2 * (ε : ℝ)) =
        CoordinateShift.translation ε (CoordinateShift.translation ε p) := by
      funext i
      simp only [CoordinateShift.translation_apply]
      ring
    have hsurvive := scaledTranslated_map_ne_zero_of_target_eq
      (M := scaledTranslatedHomology k s hs t) (p := p)
      (q := fun i => p i + 2 * (ε : ℝ))
      (q' := CoordinateShift.translation ε (CoordinateShift.translation ε p))
      (hpq' := CoordinateInterleaving.twice_le ε p)
      htarget hmap
    have hcoord : (CoordinateShift.translation ε p) 0 < u := by
      simpa [CoordinateShift.translation_apply, p, scaledTranslatedBirthA] using hmiddle
    have hzero : IsZero ((scaledTranslatedHomology k s hs u).obj
        (CoordinateShift.translation ε p)) :=
      scaledTranslatedHomology_isZero_of_coordinate_lt k s hs u _ 0 hcoord
    have hφ : I.φ.app p = 0 := hzero.eq_of_tgt _ _
    have heq := I.φ_ψ_structureMap p
    rw [hφ, zero_comp] at heq
    exact hsurvive heq.symm

/-- Every radius below both the translation gap and half the longest arm lifetime
is obstructed by an actual surviving source transition and a zero middle fiber. -/
theorem scaledTranslatedHomology_no_interleaving (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) (ε : ℝ≥0)
    (hgap : (ε : ℝ) < |t - u|)
    (hlife : (ε : ℝ) < scaledLifetime s / 2) :
    IsEmpty (CoordinateInterleaving ε (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u)) := by
  rcases le_total t u with htu | hut
  · exact scaledTranslatedHomology_no_interleaving_ordered k s hs t u ε htu hgap hlife
  · have hgap' : (ε : ℝ) < |u - t| := by simpa [abs_sub_comm] using hgap
    refine ⟨fun I => ?_⟩
    exact (scaledTranslatedHomology_no_interleaving_ordered k s hs u t ε hut
      hgap' hlife).false I.symm

/-- An explicit optimal witness at the minimum of magnitude and lifetime radii. -/
noncomputable def scaledTranslatedHomologyOptimalInterleaving (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    CoordinateInterleaving (Real.toNNReal (min |t - u| (scaledLifetime s / 2)))
      (scaledTranslatedHomology k s hs t) (scaledTranslatedHomology k s hs u) := by
  by_cases h : |t - u| ≤ scaledLifetime s / 2
  · have hm : min |t - u| (scaledLifetime s / 2) = |t - u| := min_eq_left h
    rw [hm]
    exact scaledTranslatedHomologyMagnitudeInterleaving k s hs t u
  · have hm : min |t - u| (scaledLifetime s / 2) = scaledLifetime s / 2 :=
      min_eq_right (le_of_not_ge h)
    rw [hm]
    exact scaledTranslatedHomologyLifetimeInterleaving k s hs t u

private theorem scaledTranslatedOptimalRadius_coe (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t u : ℝ) :
    ((Real.toNNReal (min |t - u| (scaledLifetime s / 2)) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (min |t - u| (scaledLifetime s / 2)) := by
  rw [ENNReal.coe_nnreal_eq]
  have hmin : 0 ≤ min |t - u| (scaledLifetime s / 2) :=
    le_min (abs_nonneg _) (div_nonneg (scaledLifetime_pos s hs).le (by norm_num))
  rw [Real.coe_toNNReal _ hmin]

private theorem scaledTranslatedHomology_distance_lower (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    ENNReal.ofReal (min |t - u| (scaledLifetime s / 2)) ≤
      coordinateInterleavingDistance (scaledTranslatedHomology k s hs t)
        (scaledTranslatedHomology k s hs u) := by
  apply le_coordinateInterleavingDistance_iff.mpr
  rintro ε ⟨I⟩
  have hrad : min |t - u| (scaledLifetime s / 2) ≤ (ε : ℝ) := by
    by_contra h
    have hsmall : (ε : ℝ) < min |t - u| (scaledLifetime s / 2) := lt_of_not_ge h
    have hgap : (ε : ℝ) < |t - u| := lt_of_lt_of_le hsmall (min_le_left _ _)
    have hlife : (ε : ℝ) < scaledLifetime s / 2 :=
      lt_of_lt_of_le hsmall (min_le_right _ _)
    exact (scaledTranslatedHomology_no_interleaving k s hs t u ε hgap hlife).false I
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hrad

/-- Exact signed-shift distance for the actual scaled PH₁ modules. -/
theorem coordinateInterleavingDistance_scaledTranslatedHomology (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    coordinateInterleavingDistance (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) =
        ENNReal.ofReal (min |t - u| (scaledLifetime s / 2)) := by
  apply le_antisymm
  · calc
      coordinateInterleavingDistance (scaledTranslatedHomology k s hs t)
          (scaledTranslatedHomology k s hs u) ≤
            ((Real.toNNReal (min |t - u| (scaledLifetime s / 2)) : ℝ≥0) : ℝ≥0∞) :=
              (scaledTranslatedHomologyOptimalInterleaving k s hs t u).distance_le
      _ = ENNReal.ofReal (min |t - u| (scaledLifetime s / 2)) :=
        scaledTranslatedOptimalRadius_coe s hs t u
  · exact scaledTranslatedHomology_distance_lower k s hs t u


end TDA.Persistence.RankResolutionDegreeTwoSimplicial
