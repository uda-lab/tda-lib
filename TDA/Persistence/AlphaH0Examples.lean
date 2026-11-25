import TDA.Persistence.AlphaH0
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Degree-zero α–Čech fixtures

The collinear cloud has a Čech edge whose endpoints are joined by two α edges.
The singleton fixture checks the transition from an empty stage to an ordinary
degree-zero class. Coincident labels remain distinct vertices, and empty inputs
have empty stages at every grade.
-/

namespace TDA.Persistence.AlphaH0Examples

open CategoryTheory TDA.Filtration TDA.Filtration.Alpha TDA.Simplicial
open scoped Matrix

noncomputable section

private def collinear : Fin 3 → ℝ := ![-1, 0, 1]

private theorem collinear_cech_outer :
    ({0,2} : Finset (Fin 3)) ∈ squaredCechFiltration collinear 1 := by
  rw [squaredCechFiltration_apply_of_nonneg collinear (by norm_num : (0 : ℝ) ≤ 1)]
  apply (Cech.mem_complex_iff _ _ _).2
  refine ⟨by decide, 0, ?_⟩
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl <;> norm_num [collinear, Real.dist_eq]

private theorem collinear_alpha_outer_absent :
    ({0,2} : Finset (Fin 3)) ∉ labelledComplex collinear 1 := by
  rw [mem_labelledComplex_iff]
  rintro ⟨_, x, hx⟩
  have ha := (hx 0 (by decide)).1 1
  have hc := (hx 2 (by decide)).1 1
  have hsa := (sq_le_sq₀ dist_nonneg dist_nonneg).2 ha
  have hsc := (sq_le_sq₀ dist_nonneg dist_nonneg).2 hc
  norm_num [collinear, Real.dist_eq, sq_abs] at hsa hsc
  nlinarith only [hsa, hsc]

private theorem collinear_alpha_left :
    ({0,1} : Finset (Fin 3)) ∈ labelledComplex collinear 1 := by
  apply (mem_labelledComplex_iff _ _ _).2
  refine ⟨by decide, -(1/2), ?_⟩
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  all_goals
    constructor
    · intro j
      fin_cases j <;> norm_num [collinear, Real.dist_eq]
    · norm_num [collinear, Real.dist_eq]

private theorem collinear_alpha_right :
    ({1,2} : Finset (Fin 3)) ∈ labelledComplex collinear 1 := by
  apply (mem_labelledComplex_iff _ _ _).2
  refine ⟨by decide, 1/2, ?_⟩
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  all_goals
    constructor
    · intro j
      fin_cases j <;> norm_num [collinear, Real.dist_eq]
    · norm_num [collinear, Real.dist_eq]

private theorem collinear_two_edge_path :
    Relation.EqvGen (fun a b : Fin 3 => ({a,b} : Finset (Fin 3)) ∈ labelledComplex collinear 1)
      0 2 :=
  Relation.EqvGen.trans 0 1 2 (Relation.EqvGen.rel 0 1 collinear_alpha_left)
    (Relation.EqvGen.rel 1 2 collinear_alpha_right)

private theorem collinear_actual_h0 :
    IsIso (simplicialHomologyIncl ℚ (labelledComplexFiltration_le_squaredCech collinear 1) 0) := by
  have h := alphaH0Comparison_isIso_app collinear ℚ 1
  rw [alphaH0Comparison_app] at h
  exact h

private theorem unitComplex_eq_singleton (K : PreAbstractSimplicialComplex Unit)
    (h : ({()} : Finset Unit) ∈ K) : K = singletonFace () := by
  ext s
  change s ∈ K ↔ s ∈ singletonFace ()
  rw [mem_singletonFace_iff]
  constructor
  · intro hs
    obtain ⟨⟨⟩, hv⟩ := (K.isRelLowerSet_faces hs).1
    ext v
    cases v
    simp [hv]
  · rintro rfl
    exact h

private def singleSite : Unit → ℝ := fun _ => 0

private theorem singleton_stages :
    labelledComplex singleSite (-1) = ⊥ ∧ squaredCechFiltration singleSite (-1) = ⊥ ∧
      labelledComplex singleSite 0 = singletonFace () ∧
      squaredCechFiltration singleSite 0 = singletonFace () := by
  have neg : (-1 : ℝ) < 0 := by norm_num
  have vertex := singleton_mem_labelledComplex singleSite () (t := 0) le_rfl
  exact ⟨labelledComplex_eq_bot_of_neg singleSite neg, squaredCechFiltration_apply_of_neg singleSite neg,
    unitComplex_eq_singleton _ vertex,
    unitComplex_eq_singleton _ (labelledComplexFiltration_le_squaredCech singleSite 0 vertex)⟩

example :
    ({()} : Finset Unit) ∈ TDA.Filtration.reindex Alpha.radius
      (Cech.complexFiltration singleSite) (-1) ∧
      ({()} : Finset Unit) ∉ squaredCechFiltration singleSite (-1) := by
  have hradius :
      TDA.Filtration.reindex Alpha.radius (Cech.complexFiltration singleSite) (-1) =
        Cech.complex singleSite 0 := by
    rw [TDA.Filtration.reindex_apply, Cech.complexFiltration_apply]
    congr 1
    exact Real.sqrt_eq_zero'.2 (by norm_num)
  constructor
  · rw [hradius]
    exact (Cech.singleton_mem_complex_iff _ _ _).2 (by norm_num)
  · rw [squaredCechFiltration_apply_of_neg singleSite (by norm_num)]
    simp

/-- The canonical target is empty below zero while the legacy reindexing is not, and the two
agree at grade zero. -/
example :
    squaredCechFiltration singleSite (-1) = ⊥ ∧
      TDA.Filtration.reindex Alpha.radius (Cech.complexFiltration singleSite) (-1) =
        Cech.complex singleSite 0 ∧
      ({()} : Finset Unit) ∈ TDA.Filtration.reindex Alpha.radius
        (Cech.complexFiltration singleSite) (-1) ∧
      TDA.Filtration.reindex Alpha.radius (Cech.complexFiltration singleSite) 0 =
        squaredCechFiltration singleSite 0 := by
  have neg : (-1 : ℝ) < 0 := by norm_num
  have hrad := reindex_radius_cech_apply_of_neg singleSite neg
  refine ⟨squaredCechFiltration_apply_of_neg singleSite neg, hrad, ?_,
    reindex_radius_cech_eq_squaredCech_of_nonneg singleSite le_rfl⟩
  rw [hrad]
  exact (Cech.singleton_mem_complex_iff _ _ _).2 (by norm_num)

private theorem singleton_h0_negative (k : Type*) [Field k] :
    Limits.IsZero (simplicialHomology (labelledComplex singleSite (-1)) k 0) ∧
      Limits.IsZero (simplicialHomology (squaredCechFiltration singleSite (-1)) k 0) := by
  rw [singleton_stages.1, singleton_stages.2.1]
  exact ⟨isZero_simplicialHomology_bot k 0, isZero_simplicialHomology_bot k 0⟩

private def singleton_h0_alpha_zero (k : Type*) [Field k] :
    simplicialHomology (labelledComplex singleSite 0) k 0 ≃ₗ[k] k := by
  rw [singleton_stages.2.2.1]
  exact simplicialSingletonH0Equiv k ()

private def singleton_h0_cech_zero (k : Type*) [Field k] :
    simplicialHomology (squaredCechFiltration singleSite 0) k 0 ≃ₗ[k] k := by
  rw [singleton_stages.2.2.2]
  exact simplicialSingletonH0Equiv k ()

private theorem singleton_alpha_structureMap_zero (k : Type*) [Field k] :
    (simplicialHomologyPModule k (labelledComplexFiltration singleSite) 0).map
      (homOfLE (show (-1 : ℝ) ≤ 0 by norm_num)) = 0 :=
  (singleton_h0_negative k).1.eq_of_src _ _

private theorem singleton_cech_structureMap_zero (k : Type*) [Field k] :
    (simplicialHomologyPModule k (squaredCechFiltration singleSite) 0).map
      (homOfLE (show (-1 : ℝ) ≤ 0 by norm_num)) = 0 :=
  (singleton_h0_negative k).2.eq_of_src _ _

private theorem singleton_grade_square (k : Type*) [Field k] :
    (simplicialHomologyPModule k (labelledComplexFiltration singleSite) 0).map
        (homOfLE (show (-1 : ℝ) ≤ 0 by norm_num)) ≫ (alphaH0Iso singleSite k).hom.app (0 : ℝ) =
      (alphaH0Iso singleSite k).hom.app (-1 : ℝ) ≫
        (simplicialHomologyPModule k (squaredCechFiltration singleSite) 0).map
          (homOfLE (show (-1 : ℝ) ≤ 0 by norm_num)) :=
  (alphaH0Iso singleSite k).hom.naturality _

private def coincidentSites : Fin 2 → ℝ := fun _ => 0

private theorem coincident_labels_zero_edge :
    ({0,1} : Finset (Fin 2)) ∈ labelledComplex coincidentSites 0 ∧
      ({0,1} : Finset (Fin 2)) ∈ squaredCechFiltration coincidentSites 0 := by
  have hi : ({0,1} : Finset (Fin 2)) ∈ labelledComplex coincidentSites 0 := by
    exact (mem_labelledComplex_iff _ _ _).2 ⟨by decide, 0, fun i _ => by simp [coincidentSites]⟩
  exact ⟨hi, labelledComplexFiltration_le_squaredCech coincidentSites 0 hi⟩

private def emptySites : Empty → ℝ := Empty.elim

private theorem empty_stages (t : ℝ) :
    labelledComplex emptySites t = ⊥ ∧ squaredCechFiltration emptySites t = ⊥ := by
  have hb (K : PreAbstractSimplicialComplex Empty) : K = ⊥ := by
    apply le_antisymm _ bot_le
    intro s hs
    obtain ⟨v, _⟩ := (K.isRelLowerSet_faces hs).1
    exact v.elim
  exact ⟨hb _, hb _⟩

end

end TDA.Persistence.AlphaH0Examples
