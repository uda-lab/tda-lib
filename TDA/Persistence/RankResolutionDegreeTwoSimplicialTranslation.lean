import TDA.Persistence.RankResolutionDegreeTwoSimplicial
import TDA.Persistence.FiniteSimplicialInterleaving

/-!
# Exact distance between uniform translates of the simplicial witness

Adding a signed real number to every face coordinate delays the actual
simplicial homology module by that amount. Its nonzero birth transition
survives every diagonal displacement strictly below one, and every
one-unit diagonal transition vanishes. These actual structure maps give
explicit optimal interleavings and the distance `min |t-s| (1/2)`.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory CategoryTheory.Limits TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal

/-- Pull back a parameter by a signed delay. Positive delays subtract from the index. -/
def translationPullback (t : ℝ) : (Fin 2 → ℝ) →o (Fin 2 → ℝ) :=
  OrderHomClass.toOrderHom (OrderIso.addRight (fun _ : Fin 2 => -t))

@[simp] theorem translationPullback_apply (t : ℝ) (p : Fin 2 → ℝ) (i : Fin 2) :
    translationPullback t p i = p i - t := rfl

/-- Add the same signed real delay to every coordinate of every actual face. -/
def translatedGrading (t : ℝ) : FiniteGraded boundaryTetrahedron 2 where
  grade σ i := boundaryTetrahedronGrading.grade σ i + t
  mono h i := by
    have hg := boundaryTetrahedronGrading.mono h i
    dsimp only
    linarith

@[simp] theorem translatedGrading_grade (t : ℝ)
    (σ : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    (translatedGrading t).grade σ i = boundaryTetrahedronGrading.grade σ i + t := rfl

@[simp] theorem translatedGrading_zero : translatedGrading 0 = boundaryTetrahedronGrading := by
  apply FiniteGraded.ext
  intro σ
  funext i
  simp

/-- Face translation is exactly pullback of the original sublevel parameter. -/
theorem translatedGrading_sublevel (t : ℝ) (p : Fin 2 → ℝ) :
    (translatedGrading t).sublevel p =
      boundaryTetrahedronGrading.sublevel (translationPullback t p) := by
  apply le_antisymm
  · rintro σ ⟨hσ, hp⟩
    exact ⟨hσ, fun i => le_sub_iff_add_le.mpr (hp i)⟩
  · rintro σ ⟨hσ, hp⟩
    exact ⟨hσ, fun i => le_sub_iff_add_le.mp (hp i)⟩

/-- The actual inclusion-induced degree-one homology of the translated input. -/
noncomputable abbrev translatedHomology (k : Type u) [Field k] (t : ℝ) :
    PModule.{u,0,u} k (Fin 2 → ℝ) :=
  finiteSimplicialHomology k (translatedGrading t) 1

@[simp] theorem translatedHomology_zero (k : Type u) [Field k] :
    translatedHomology k 0 = finiteSimplicialHomology k boundaryTetrahedronGrading 1 := by
  simp only [translatedHomology, translatedGrading_zero]

/-- The actual translated homology is naturally the pullback of the original homology. -/
noncomputable def translatedHomologyReindexIso (k : Type u) [Field k] (t : ℝ) :
    translatedHomology k t ≅
      reindex (translationPullback t) (finiteSimplicialHomology k boundaryTetrahedronGrading 1) := by
  have hfil : (translatedGrading t).sublevelFiltration =
      TDA.Filtration.reindex (translationPullback t)
        boundaryTetrahedronGrading.sublevelFiltration := by
    apply DFunLike.ext
    intro p
    exact translatedGrading_sublevel t p
  unfold translatedHomology finiteSimplicialHomology
  rw [hfil]
  exact Iso.refl _

/-- The translated realization uses the existing natural realization of actual homology. -/
noncomputable def translatedRealIso (k : Type u) [Field k] (t : ℝ) :
    translatedHomology k t ≅ reindex (translationPullback t) (realModule (k := k)) :=
  (translatedHomologyReindexIso k t).trans
    (Functor.isoWhiskerLeft (translationPullback t).toFunctor (realIso k))

/-- The realization comparison commutes with every actual structure map. -/
theorem translatedRealIso_structureMap (k : Type u) [Field k] (t : ℝ)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (translatedHomology k t) hpq ≫ (translatedRealIso k t).hom.app q =
      (translatedRealIso k t).hom.app p ≫
        structureMap (realModule (k := k)) ((translationPullback t).monotone' hpq) :=
  (translatedRealIso k t).hom.naturality (homOfLE hpq)

/-- Each translate retains an original finite graded-free presentation from its finite input. -/
theorem translatedHomology_finitelyPresented (k : Type u) [Field k] (t : ℝ) :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (translatedHomology k t) :=
  finiteSimplicialHomology_finitelyPresented k (translatedGrading t) 1

private theorem supportOrdConnected : support.OrdConnected where
  out' := by
    intro x hx z hz y hy
    refine ⟨?_, hy.2.trans hz.2⟩
    rcases hx.1 with hax | hbx
    · exact Or.inl (hax.trans hy.1)
    · exact Or.inr (hbx.trans hy.1)

private theorem a_mem_support : a ∈ support := by
  change (a ≤ a ∨ b ≤ a) ∧ a ≤ c
  refine ⟨Or.inl le_rfl, ?_⟩
  change grid.embedding a ≤ grid.embedding c
  rw [grid_embedding_a, grid_embedding_c]
  intro i
  fin_cases i <;> norm_num

private theorem b_mem_support : b ∈ support := by
  change (a ≤ b ∨ b ≤ b) ∧ b ≤ c
  refine ⟨Or.inr le_rfl, ?_⟩
  change grid.embedding b ≤ grid.embedding c
  rw [grid_embedding_b, grid_embedding_c]
  intro i
  fin_cases i <;> norm_num

private theorem coordinate_cases (p : grid.Point) (i : Fin 2) :
    (p i).val = 0 ∨ (p i).val = 1 ∨ (p i).val = 2 := by
  have hp := (p i).property
  simpa only [grid, gridValues, Finset.mem_insert, Finset.mem_singleton] using hp

private theorem noLowerPoint_of_first_neg (p : Fin 2 → ℝ) (hp : p 0 < 0) :
    ¬ grid.HasLowerPoint p := by
  rintro ⟨q, hq⟩
  have hq0 : (q 0).val ≤ p 0 := hq 0
  rcases coordinate_cases q 0 with h | h | h <;> rw [h] at hq0 <;> linarith

private theorem noLowerPoint_of_second_neg (p : Fin 2 → ℝ) (hp : p 1 < 0) :
    ¬ grid.HasLowerPoint p := by
  rintro ⟨q, hq⟩
  have hq1 : (q 1).val ≤ p 1 := hq 1
  rcases coordinate_cases q 1 with h | h | h <;> rw [h] at hq1 <;> linarith

/-- The actual unshifted H₁ fiber vanishes below the second-coordinate birth. -/
theorem homology_isZero_of_second_neg (k : Type u) [Field k]
    (p : Fin 2 → ℝ) (hp : p 1 < 0) :
    IsZero ((finiteSimplicialHomology k boundaryTetrahedronGrading 1).obj p) := by
  apply IsZero.of_iso
    (grid.isZero_obj_of_not_hasLowerPoint (finiteModule (k := k)) p
      (noLowerPoint_of_second_neg p hp))
    ((realIso k).app p)

private theorem floor_eq_a_of_bounds (p : Fin 2 → ℝ) (hp : grid.HasLowerPoint p)
    (h0 : 0 ≤ p 0) (h1 : p 0 < 1) (h2 : 1 ≤ p 1) (h3 : p 1 < 2) :
    grid.floor p hp = a := by
  apply (grid.floor_eq_iff p hp a).mpr
  constructor
  · rw [grid_embedding_a]
    intro i
    fin_cases i <;> simpa using (by assumption : _)
  · intro q hq
    change grid.embedding q ≤ grid.embedding a
    rw [grid_embedding_a]
    intro i
    fin_cases i
    · have hq0 : (q 0).val ≤ p 0 := hq 0
      change (q 0).val ≤ 0
      rcases coordinate_cases q 0 with h | h | h <;> rw [h] <;> linarith
    · have hq1 : (q 1).val ≤ p 1 := hq 1
      change (q 1).val ≤ 1
      rcases coordinate_cases q 1 with h | h | h <;> rw [h] <;> linarith

private theorem floor_eq_b_of_bounds (p : Fin 2 → ℝ) (hp : grid.HasLowerPoint p)
    (h0 : 1 ≤ p 0) (h1 : p 0 < 2) (h2 : 0 ≤ p 1) (h3 : p 1 < 1) :
    grid.floor p hp = b := by
  apply (grid.floor_eq_iff p hp b).mpr
  constructor
  · rw [grid_embedding_b]
    intro i
    fin_cases i <;> simpa using (by assumption : _)
  · intro q hq
    change grid.embedding q ≤ grid.embedding b
    rw [grid_embedding_b]
    intro i
    fin_cases i
    · have hq0 : (q 0).val ≤ p 0 := hq 0
      change (q 0).val ≤ 1
      rcases coordinate_cases q 0 with h | h | h <;> rw [h] <;> linarith
    · have hq1 : (q 1).val ≤ p 1 := hq 1
      change (q 1).val ≤ 0
      rcases coordinate_cases q 1 with h | h | h <;> rw [h] <;> linarith

private theorem finite_map_zero (k : Type u) [Field k]
    {p q : grid.Point} (hpq : p ≤ q) (hnot : ¬ (p ∈ support ∧ q ∈ support)) :
    structureMap (finiteModule (k := k)) hpq = 0 := by
  apply ModuleCat.hom_ext
  exact SupportInterval.structureMap_eq_zero_of_not_mem support supportOrdConnected hpq hnot

private theorem finite_map_ne_zero (k : Type u) [Field k]
    {p q : grid.Point} (hpq : p ≤ q) (hp : p ∈ support) (hq : q ∈ support) :
    structureMap (finiteModule (k := k)) hpq ≠ 0 := by
  intro hz
  have hz' : structureMapLinear (SupportInterval.module (k := k) support supportOrdConnected) hpq = 0 :=
    congrArg ModuleCat.Hom.hom hz
  exact (SupportInterval.structureMap_eq_zero_iff support supportOrdConnected hpq).mp hz' ⟨hp, hq⟩

private theorem lan_map_zero (k : Type u) [Field k] {p q : Fin 2 → ℝ}
    (hpq : p ≤ q) (hp : grid.HasLowerPoint p) (hq : grid.HasLowerPoint q)
    (hz : structureMap (finiteModule (k := k)) (grid.floor_mono hpq hp hq) = 0) :
    structureMap (realModule (k := k)) hpq = 0 := by
  apply (cancel_mono (grid.appIso (finiteModule (k := k)) q hq).hom).mp
  rw [grid.appIso_structureMap (finiteModule (k := k)) hpq hp hq, hz, comp_zero, zero_comp]

private theorem lan_map_ne_zero (k : Type u) [Field k] {p q : Fin 2 → ℝ}
    (hpq : p ≤ q) (hp : grid.HasLowerPoint p) (hq : grid.HasLowerPoint q)
    (hne : structureMap (finiteModule (k := k)) (grid.floor_mono hpq hp hq) ≠ 0) :
    structureMap (realModule (k := k)) hpq ≠ 0 := by
  intro hz
  apply hne
  apply (cancel_epi (grid.appIso (finiteModule (k := k)) p hp).hom).mp
  rw [← grid.appIso_structureMap (finiteModule (k := k)) hpq hp hq, hz, zero_comp, comp_zero]

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

private theorem nonneg_of_hasLowerPoint (p : Fin 2 → ℝ) (hp : grid.HasLowerPoint p)
    (i : Fin 2) : 0 ≤ p i := by
  obtain ⟨x, hx⟩ := hp
  have hxi : (x i).val ≤ p i := hx i
  rcases coordinate_cases x i with h | h | h
  · rw [h] at hxi
    linarith
  · rw [h] at hxi
    linarith
  · rw [h] at hxi
    linarith

private theorem floor_le_c_of_upper (p : Fin 2 → ℝ) (hp : grid.HasLowerPoint p)
    (h0 : p 0 < 2) (h1 : p 1 < 2) : grid.floor p hp ≤ c := by
  intro i
  change (grid.floor p hp i).val ≤ (c i).val
  have hc : (c i).val = 1 := by
    have h := congrFun grid_embedding_c i
    simpa only [grid.embedding_apply] using h
  have hle : (grid.floor p hp i).val ≤ p i := grid.floor_le p hp i
  rcases coordinate_cases (grid.floor p hp) i with h | h | h
  · rw [h, hc]
    norm_num
  · rw [h, hc]
  · have hpi : p i < 2 := by fin_cases i <;> assumption
    rw [h] at hle
    linarith

/-- A structure map of the tetrahedron's PH₁ persistence module is nonzero
exactly when its source is in the lower support and its target is below both
cap deaths. -/
theorem homology_structureMap_ne_zero_iff (k : Type u) [Field k]
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1) hpq ≠ 0 ↔
      0 ≤ p 0 ∧ 0 ≤ p 1 ∧ (1 ≤ p 0 ∨ 1 ≤ p 1) ∧ q 0 < 2 ∧ q 1 < 2 := by
  constructor
  · intro hne
    have hreal : structureMap (realModule (k := k)) hpq ≠ 0 :=
      map_ne_zero_of_iso (realIso k).symm hpq hne
    have hp : grid.HasLowerPoint p := by
      by_contra hn
      exact hreal ((grid.isZero_obj_of_not_hasLowerPoint
        (finiteModule (k := k)) p hn).eq_of_src _ _)
    have hq := grid.hasLowerPoint_mono hpq hp
    have hfinite : structureMap (finiteModule (k := k))
        (grid.floor_mono hpq hp hq) ≠ 0 := by
      intro hz
      exact hreal (lan_map_zero k hpq hp hq hz)
    have hfp : grid.floor p hp ∈ support := by
      by_contra hn
      apply hfinite
      apply finite_map_zero
      intro hboth
      exact hn hboth.1
    have hfq : grid.floor q hq ∈ support := by
      by_contra hn
      apply hfinite
      apply finite_map_zero
      intro hboth
      exact hn hboth.2
    have hp0 : 0 ≤ p 0 := nonneg_of_hasLowerPoint p hp 0
    have hp1 : 0 ≤ p 1 := nonneg_of_hasLowerPoint p hp 1
    have hparm : 1 ≤ p 0 ∨ 1 ≤ p 1 := by
      rcases hfp.1 with ha | hb
      · have hle : grid.embedding a ≤ p :=
          (grid.embedding.monotone ha).trans (grid.floor_le p hp)
        rw [grid_embedding_a] at hle
        have h := hle 1
        norm_num at h
        exact Or.inr h
      · have hle : grid.embedding b ≤ p :=
          (grid.embedding.monotone hb).trans (grid.floor_le p hp)
        rw [grid_embedding_b] at hle
        have h := hle 0
        norm_num at h
        exact Or.inl h
    have hq0 : q 0 < 2 := by
      by_contra hn
      have htwo : 2 ≤ q 0 := le_of_not_gt hn
      have heq : grid.embedding e ≤ q := by
        rw [grid_embedding_e]
        intro i
        fin_cases i
        · exact htwo
        · exact nonneg_of_hasLowerPoint q hq 1
      have hec : e ≤ c := (grid.le_floor q hq heq).trans hfq.2
      have hle := grid.embedding.monotone hec
      rw [grid_embedding_e, grid_embedding_c] at hle
      have h := hle 0
      norm_num at h
    have hq1 : q 1 < 2 := by
      by_contra hn
      have htwo : 2 ≤ q 1 := le_of_not_gt hn
      have hdq : grid.embedding d ≤ q := by
        rw [grid_embedding_d]
        intro i
        fin_cases i
        · exact nonneg_of_hasLowerPoint q hq 0
        · exact htwo
      have hdc : d ≤ c := (grid.le_floor q hq hdq).trans hfq.2
      have hle := grid.embedding.monotone hdc
      rw [grid_embedding_d, grid_embedding_c] at hle
      have h := hle 1
      norm_num at h
    exact ⟨hp0, hp1, hparm, hq0, hq1⟩
  · rintro ⟨hp0, hp1, hparm, hq0, hq1⟩
    have hp : grid.HasLowerPoint p := by
      rcases hparm with h0 | h1
      · refine ⟨b, ?_⟩
        rw [grid_embedding_b]
        intro i
        fin_cases i
        · exact h0
        · exact hp1
      · refine ⟨a, ?_⟩
        rw [grid_embedding_a]
        intro i
        fin_cases i
        · exact hp0
        · exact h1
    have hq := grid.hasLowerPoint_mono hpq hp
    have hp0lt : p 0 < 2 := lt_of_le_of_lt (hpq 0) hq0
    have hp1lt : p 1 < 2 := lt_of_le_of_lt (hpq 1) hq1
    rcases hparm with h0 | h1
    · have hArmP : grid.embedding b ≤ p := by
        rw [grid_embedding_b]
        intro i
        fin_cases i
        · exact h0
        · exact hp1
      have hArmQ : grid.embedding b ≤ q := hArmP.trans hpq
      have hfp : grid.floor p hp ∈ support := by
        change (a ≤ grid.floor p hp ∨ b ≤ grid.floor p hp) ∧ grid.floor p hp ≤ c
        exact ⟨Or.inr (grid.le_floor p hp hArmP),
          floor_le_c_of_upper p hp hp0lt hp1lt⟩
      have hfq : grid.floor q hq ∈ support := by
        change (a ≤ grid.floor q hq ∨ b ≤ grid.floor q hq) ∧ grid.floor q hq ≤ c
        exact ⟨Or.inr (grid.le_floor q hq hArmQ),
          floor_le_c_of_upper q hq hq0 hq1⟩
      have hfinite := finite_map_ne_zero k (grid.floor_mono hpq hp hq) hfp hfq
      exact map_ne_zero_of_iso (realIso k) hpq (lan_map_ne_zero k hpq hp hq hfinite)
    · have hArmP : grid.embedding a ≤ p := by
        rw [grid_embedding_a]
        intro i
        fin_cases i
        · exact hp0
        · exact h1
      have hArmQ : grid.embedding a ≤ q := hArmP.trans hpq
      have hfp : grid.floor p hp ∈ support := by
        change (a ≤ grid.floor p hp ∨ b ≤ grid.floor p hp) ∧ grid.floor p hp ≤ c
        exact ⟨Or.inl (grid.le_floor p hp hArmP),
          floor_le_c_of_upper p hp hp0lt hp1lt⟩
      have hfq : grid.floor q hq ∈ support := by
        change (a ≤ grid.floor q hq ∨ b ≤ grid.floor q hq) ∧ grid.floor q hq ≤ c
        exact ⟨Or.inl (grid.le_floor q hq hArmQ),
          floor_le_c_of_upper q hq hq0 hq1⟩
      have hfinite := finite_map_ne_zero k (grid.floor_mono hpq hp hq) hfp hfq
      exact map_ne_zero_of_iso (realIso k) hpq (lan_map_ne_zero k hpq hp hq hfinite)

/-- The actual unshifted H₁ map from the second arm survives every subunit delay. -/
theorem homology_secondBirth_structureMap_ne_zero (k : Type u) [Field k]
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    structureMap (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      (show grid.embedding b ≤ (fun i => grid.embedding b i + r) from
        fun _ => le_add_of_nonneg_right hr0) ≠ 0 := by
  apply map_ne_zero_of_iso (realIso k)
  have hp : grid.HasLowerPoint (grid.embedding b) := by
    exact ⟨b, fun _ => le_rfl⟩
  have hq : grid.HasLowerPoint (fun i => grid.embedding b i + r) := by
    exact ⟨b, fun _ => le_add_of_nonneg_right hr0⟩
  have hp0 : grid.embedding b 0 = 1 := by
    rw [grid_embedding_b]
    norm_num
  have hp1 : grid.embedding b 1 = 0 := by
    rw [grid_embedding_b]
    norm_num
  have hq0 : (fun i => grid.embedding b i + r) 0 = 1 + r := by
    rw [grid_embedding_b]
    norm_num
  have hq1 : (fun i => grid.embedding b i + r) 1 = r := by
    rw [grid_embedding_b]
    norm_num
  have hfp : grid.floor (grid.embedding b) hp = b := by
    apply floor_eq_b_of_bounds
    · rw [hp0]
    · rw [hp0]
      norm_num
    · rw [hp1]
    · rw [hp1]
      norm_num
  have hfq : grid.floor (fun i => grid.embedding b i + r) hq = b := by
    apply floor_eq_b_of_bounds
    · change 1 ≤ (fun i => grid.embedding b i + r) 0
      rw [hq0]
      linarith
    · change (fun i => grid.embedding b i + r) 0 < 2
      rw [hq0]
      linarith
    · change 0 ≤ (fun i => grid.embedding b i + r) 1
      rw [hq1]
      exact hr0
    · change (fun i => grid.embedding b i + r) 1 < 1
      rw [hq1]
      exact hr1
  apply lan_map_ne_zero k _ hp hq
  apply finite_map_ne_zero
  · rw [hfp]
    exact b_mem_support
  · rw [hfq]
    exact b_mem_support

private theorem lan_diagonal_one_zero (k : Type u) [Field k]
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) (hstep : ∀ i, q i = p i + 1) :
    structureMap (realModule (k := k)) hpq = 0 := by
  by_cases hp : grid.HasLowerPoint p
  · have hq := grid.hasLowerPoint_mono hpq hp
    apply lan_map_zero k hpq hp hq
    apply finite_map_zero
    rintro ⟨hu, hv⟩
    have hu' : grid.embedding (grid.floor p hp) ≤ p := grid.floor_le p hp
    have hv' : grid.floor q hq ≤ c := hv.2
    rcases hu.1 with hau | hbu
    · have ha : grid.embedding a ≤ p := (grid.embedding.monotone hau).trans hu'
      rw [grid_embedding_a] at ha
      have hd : grid.embedding d ≤ q := by
        rw [grid_embedding_d]
        intro i
        have hi := ha i
        have hs := hstep i
        fin_cases i <;> norm_num at hi hs ⊢ <;> linarith
      have hdc := (grid.le_floor q hq hd).trans hv'
      have hreal : grid.embedding d ≤ grid.embedding c := grid.embedding.monotone hdc
      rw [grid_embedding_d, grid_embedding_c] at hreal
      have hh := hreal 1
      norm_num at hh
    · have hb : grid.embedding b ≤ p := (grid.embedding.monotone hbu).trans hu'
      rw [grid_embedding_b] at hb
      have he : grid.embedding e ≤ q := by
        rw [grid_embedding_e]
        intro i
        have hi := hb i
        have hs := hstep i
        fin_cases i <;> norm_num at hi hs ⊢ <;> linarith
      have hec := (grid.le_floor q hq he).trans hv'
      have hreal : grid.embedding e ≤ grid.embedding c := grid.embedding.monotone hec
      rw [grid_embedding_e, grid_embedding_c] at hreal
      have hh := hreal 0
      norm_num at hh
  · exact (grid.isZero_obj_of_not_hasLowerPoint (finiteModule (k := k)) p hp).eq_of_src _ _

private theorem translated_map_zero_of_step (k : Type u) [Field k] (t : ℝ)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) (hstep : ∀ i, q i = p i + 1) :
    structureMap (translatedHomology k t) hpq = 0 := by
  apply map_zero_of_iso (translatedRealIso k t)
  change structureMap (realModule (k := k)) _ = 0
  apply lan_diagonal_one_zero
  intro i
  change q i - t = (p i - t) + 1
  rw [hstep]
  ring

/-- Every actual translated module kills its one-unit diagonal transition. -/
theorem translatedHomology_diagonal_one_zero (k : Type u) [Field k] (t : ℝ)
    (p : Fin 2 → ℝ) :
    structureMap (translatedHomology k t)
      (show p ≤ (fun i => p i + 1) from fun _ => le_add_of_nonneg_right (by norm_num)) = 0 :=
  translated_map_zero_of_step k t _ (fun _ => rfl)

/-- The first cycle birth after translating every face coordinate. -/
noncomputable def translatedBirth (t : ℝ) : Fin 2 → ℝ := fun i => grid.embedding a i + t

@[simp] theorem translatedBirth_first (t : ℝ) : translatedBirth t 0 = t := by
  unfold translatedBirth
  rw [grid_embedding_a]
  norm_num

@[simp] theorem translatedBirth_second (t : ℝ) : translatedBirth t 1 = 1 + t := by
  unfold translatedBirth
  rw [grid_embedding_a]
  norm_num

/-- Before the first coordinate birth, the actual translated homology fiber is zero. -/
theorem translatedHomology_isZero_of_first_lt (k : Type u) [Field k]
    (t : ℝ) (p : Fin 2 → ℝ) (hp : p 0 < t) :
    IsZero ((translatedHomology k t).obj p) := by
  apply IsZero.of_iso
    (grid.isZero_obj_of_not_hasLowerPoint (finiteModule (k := k))
      (translationPullback t p) (noLowerPoint_of_first_neg _ (by
        simp only [translationPullback_apply]
        linarith)))
    ((translatedRealIso k t).app p)

private theorem translated_birth_map_ne_zero_of_step (k : Type u) [Field k]
    (t r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {q : Fin 2 → ℝ} (hbq : translatedBirth t ≤ q)
    (hstep : ∀ i, q i = translatedBirth t i + r) :
    structureMap (translatedHomology k t) hbq ≠ 0 := by
  apply map_ne_zero_of_iso (translatedRealIso k t)
  change structureMap (realModule (k := k)) _ ≠ 0
  have hp : grid.HasLowerPoint (translationPullback t (translatedBirth t)) := by
    refine ⟨a, fun i => ?_⟩
    simp only [translationPullback_apply, translatedBirth]
    linarith
  have hq : grid.HasLowerPoint (translationPullback t q) := by
    refine ⟨a, fun i => ?_⟩
    simp only [translationPullback_apply, hstep, translatedBirth]
    linarith
  have hp0 : translationPullback t (translatedBirth t) 0 = 0 := by simp
  have hp1 : translationPullback t (translatedBirth t) 1 = 1 := by simp
  have hq0 : translationPullback t q 0 = r := by
    simp only [translationPullback_apply, hstep, translatedBirth_first]
    ring
  have hq1 : translationPullback t q 1 = 1 + r := by
    simp only [translationPullback_apply, hstep, translatedBirth_second]
    ring
  have hfp : grid.floor _ hp = a := by
    apply floor_eq_a_of_bounds <;> simp only [hp0, hp1] <;> norm_num
  have hfq : grid.floor _ hq = a := by
    apply floor_eq_a_of_bounds <;> simp only [hq0, hq1] <;> linarith
  apply lan_map_ne_zero k _ hp hq
  apply finite_map_ne_zero
  · rw [hfp]
    exact a_mem_support
  · rw [hfq]
    exact a_mem_support

/-- The actual first-cycle map survives every nonnegative displacement strictly below one. -/
theorem translatedHomology_birth_structureMap_ne_zero (k : Type u) [Field k]
    (t r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    structureMap (translatedHomology k t)
      (show translatedBirth t ≤ (fun i => translatedBirth t i + r) from
        fun _ => le_add_of_nonneg_right hr0) ≠ 0 :=
  translated_birth_map_ne_zero_of_step k t r hr0 hr1 _ (fun _ => rfl)

/-- The actual cycle birth fiber is nonzero, even though every one-unit transition vanishes. -/
theorem translatedHomology_birth_not_isZero (k : Type u) [Field k] (t : ℝ) :
    ¬ IsZero ((translatedHomology k t).obj (translatedBirth t)) := by
  intro hz
  exact translatedHomology_birth_structureMap_ne_zero k t 0 (by norm_num) (by norm_num)
    (hz.eq_of_src _ _)

/-- The translated face coordinate error is bounded by the translation gap. -/
theorem translatedGrading_grade_error (s t : ℝ)
    (σ : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    |(translatedGrading s).grade σ i - (translatedGrading t).grade σ i| ≤
      (‖t - s‖₊ : ℝ) := by
  rw [translatedGrading_grade, translatedGrading_grade,
    show boundaryTetrahedronGrading.grade σ i + s -
      (boundaryTetrahedronGrading.grade σ i + t) = s - t by ring]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_sub_comm]
  exact le_rfl

/-- Inclusion-induced interleaving at the magnitude of the signed translation gap. -/
noncomputable def translatedHomologyMagnitudeInterleaving (k : Type u) [Field k]
    (s t : ℝ) : CoordinateInterleaving ‖t - s‖₊ (translatedHomology k s)
      (translatedHomology k t) :=
  finiteSimplicialHomology_interleaving k (translatedGrading s) (translatedGrading t) 1
    (translatedGrading_grade_error s t)

/-- The magnitude witness's forward map is the actual shifted sublevel inclusion. -/
@[simp] theorem translatedHomologyMagnitudeInterleaving_φ_app (k : Type u) [Field k]
    (s t : ℝ) (p : Fin 2 → ℝ) :
    (translatedHomologyMagnitudeInterleaving k s t).φ.app p =
      simplicialHomologyIncl k ((translatedGrading s).sublevel_le_translation_of_error
        (translatedGrading t) (translatedGrading_grade_error s t) p) 1 :=
  finiteSimplicialHomology_interleaving_φ_app k _ _ 1 _ p

/-- The magnitude witness's reverse map is the actual reverse shifted inclusion. -/
@[simp] theorem translatedHomologyMagnitudeInterleaving_ψ_app (k : Type u) [Field k]
    (s t : ℝ) (p : Fin 2 → ℝ) :
    (translatedHomologyMagnitudeInterleaving k s t).ψ.app p =
      simplicialHomologyIncl k ((translatedGrading t).sublevel_le_translation_of_error
        (translatedGrading s) (fun σ i => by
          simpa only [abs_sub_comm] using translatedGrading_grade_error s t σ i) p) 1 :=
  finiteSimplicialHomology_interleaving_ψ_app k _ _ 1 _ p

/-- Zero natural maps interleave any two translates at one half of the diagonal lifetime. -/
noncomputable def translatedHomologyHalfInterleaving (k : Type u) [Field k]
    (s t : ℝ) : CoordinateInterleaving (1 / 2) (translatedHomology k s)
      (translatedHomology k t) :=
  CoordinateInterleaving.ofStructureMapEquations 0 0
    (fun p => by
      change (0 : (translatedHomology k s).obj p ⟶
        (translatedHomology k t).obj (CoordinateShift.translation (1/2) p)) ≫ 0 = _
      rw [zero_comp]
      symm
      apply translated_map_zero_of_step
      intro i
      simp only [CoordinateShift.translation_apply]
      norm_num
      ring)
    (fun p => by
      change (0 : (translatedHomology k t).obj p ⟶
        (translatedHomology k s).obj (CoordinateShift.translation (1/2) p)) ≫ 0 = _
      rw [zero_comp]
      symm
      apply translated_map_zero_of_step
      intro i
      simp only [CoordinateShift.translation_apply]
      norm_num
      ring)

@[simp] theorem translatedHomologyHalfInterleaving_φ (k : Type u) [Field k]
    (s t : ℝ) : (translatedHomologyHalfInterleaving k s t).φ = 0 := rfl

@[simp] theorem translatedHomologyHalfInterleaving_ψ (k : Type u) [Field k]
    (s t : ℝ) : (translatedHomologyHalfInterleaving k s t).ψ = 0 := rfl

/-- An actual optimal witness, choosing shifted inclusions or the half-radius zero maps. -/
noncomputable def translatedHomologyOptimalInterleaving (k : Type u) [Field k]
    (s t : ℝ) : CoordinateInterleaving (min ‖t - s‖₊ (1 / 2))
      (translatedHomology k s) (translatedHomology k t) := by
  by_cases h : ‖t - s‖₊ ≤ (1 / 2 : ℝ≥0)
  · rw [min_eq_left h]
    exact translatedHomologyMagnitudeInterleaving k s t
  · rw [min_eq_right (le_of_not_ge h)]
    exact translatedHomologyHalfInterleaving k s t

/-- A subcritical candidate factors through a zero fiber but must recover a nonzero birth map. -/
theorem translatedHomology_no_interleaving (k : Type u) [Field k]
    (s t : ℝ) (ε : ℝ≥0) (hgap : (ε : ℝ) < t - s) (hlife : 2 * (ε : ℝ) < 1) :
    IsEmpty (CoordinateInterleaving ε (translatedHomology k s) (translatedHomology k t)) := by
  refine ⟨fun I => ?_⟩
  have hzero : IsZero ((translatedHomology k t).obj
      (CoordinateShift.translation ε (translatedBirth s))) := by
    apply translatedHomology_isZero_of_first_lt
    simp only [CoordinateShift.translation_apply, translatedBirth_first]
    linarith
  have hf : I.φ.app (translatedBirth s) = 0 := hzero.eq_of_tgt _ _
  have hsurvive : structureMap (translatedHomology k s)
      (CoordinateInterleaving.twice_le ε (translatedBirth s)) ≠ 0 := by
    apply translated_birth_map_ne_zero_of_step k s (2 * (ε : ℝ))
      (by positivity) hlife
    intro i
    simp only [CoordinateShift.translation_apply]
    ring
  exact hsurvive (by erw [← I.φ_ψ_structureMap (translatedBirth s), hf, zero_comp])

private theorem optimalRadius_coe (s t : ℝ) :
    ((min ‖t - s‖₊ (1 / 2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (min |t - s| (1 / 2)) := by
  rw [ENNReal.coe_nnreal_eq]
  simp [Real.norm_eq_abs]

private theorem distance_lower_of_le (k : Type u) [Field k] (s t : ℝ) (hst : s ≤ t) :
    ENNReal.ofReal (min |t - s| (1 / 2)) ≤
      coordinateInterleavingDistance (translatedHomology k s) (translatedHomology k t) := by
  apply le_coordinateInterleavingDistance_iff.mpr
  rintro ε ⟨I⟩
  have hr : min |t - s| (1 / 2 : ℝ) ≤ (ε : ℝ) := by
    by_contra h
    have hlt : (ε : ℝ) < min |t - s| (1 / 2 : ℝ) := lt_of_not_ge h
    have hgap : (ε : ℝ) < t - s := by
      have hh := hlt.trans_le (min_le_left _ _)
      rwa [abs_of_nonneg (sub_nonneg.mpr hst)] at hh
    have hlife : 2 * (ε : ℝ) < 1 := by
      have hh := hlt.trans_le (min_le_right _ _)
      linarith
    exact (translatedHomology_no_interleaving k s t ε hgap hlife).false I
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr

/-- The exact extended coordinate interleaving distance between any two signed translates. -/
theorem coordinateInterleavingDistance_translatedHomology (k : Type u) [Field k]
    (s t : ℝ) :
    coordinateInterleavingDistance (translatedHomology k s) (translatedHomology k t) =
      ENNReal.ofReal (min |t - s| (1 / 2)) := by
  have upper (v w : ℝ) :
      coordinateInterleavingDistance (translatedHomology k v) (translatedHomology k w) ≤
        ENNReal.ofReal (min |w - v| (1 / 2)) := by
    simpa only [optimalRadius_coe] using (translatedHomologyOptimalInterleaving k v w).distance_le
  rcases le_total s t with hst | hts
  · exact le_antisymm (upper s t) (distance_lower_of_le k s t hst)
  · rw [coordinateInterleavingDistance_comm]
    simpa only [abs_sub_comm] using
      le_antisymm (upper t s) (distance_lower_of_le k t s hts)

/-- The zero-parameter specialization computes distance from the existing unmodified realization. -/
theorem coordinateInterleavingDistance_original_translatedHomology (k : Type u) [Field k]
    (t : ℝ) :
    coordinateInterleavingDistance (finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      (translatedHomology k t) = ENNReal.ofReal (min |t| (1 / 2)) := by
  simpa only [translatedHomology_zero, sub_zero] using
    coordinateInterleavingDistance_translatedHomology k 0 t

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
