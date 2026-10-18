import TDA.Persistence.EssentialVanishing
import TDA.Persistence.TriangleCechRipsExamples
import TDA.Persistence.TotalPersistenceRipsCechExamples
import TDA.Persistence.SublevelConstructibleExamples

set_option autoImplicit false

/-!
# Essential-bar vanishing fixtures

These examples cross-check the full-complex essential-bar theorems against the explicit triangle,
two-point, repeated-label, hollow-triangle, filled-triangle, and persistence-image fixtures.
-/

namespace TDA.Persistence.EssentialVanishingExamples

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration TDA.Persistence
open TDA.Persistence.Examples
open TDA.Persistence.FiniteConstructible
open TDA.Persistence.SublevelConstructibleExamples
open TDA.Persistence.TriangleCechRipsExamples
open TDA.Persistence.TotalPersistenceRipsCechExamples
open TDA.Persistence.Reduction.Examples
open TDA.Filtration.Cech.Examples
open Real
open scoped NNReal ENNReal

noncomputable section

/-! ### P1: the library triangle -/

/-- The library triangle has no essential Čech bar in degree one. -/
theorem triangle_cech_essentialPart_one_eq_zero :
    essentialPart (dgm (ZMod 2) cechT 1).points = 0 :=
  Cech.essentialPart_dgm_eq_zero (k := ZMod 2) Triangle.pts (by norm_num)

/-- The library triangle has no essential Rips bar in degree one. -/
theorem triangle_rips_essentialPart_one_eq_zero :
    essentialPart (dgm (ZMod 2) ripsT 1).points = 0 :=
  Rips.essentialPart_dgm_eq_zero (k := ZMod 2) Triangle.metric (by norm_num)

/-- The explicit library-triangle Čech degree-one finite part is the bar `(√5/2, 5/4)`. -/
theorem triangle_cech_finitePart_one_eq_singleton :
    finitePart (dgm (ZMod 2) cechT 1).points = {(√5 / 2, 5 / 4)} := by
  rw [triangle_cech_dgm_one]
  rfl

/-- The explicit library-triangle Rips degree-one finite part is empty. -/
theorem triangle_rips_finitePart_one_eq_zero :
    finitePart (dgm (ZMod 2) ripsT 1).points = 0 := by
  rw [triangle_rips_dgm_one]
  rfl

/-- Item 18 identifies the library-triangle Čech degree-one diagram with its finite part. -/
theorem triangle_cech_dgm_one_eq_finitePart_embedding :
    (dgm (ZMod 2) cechT 1).points =
      (finitePart (dgm (ZMod 2) cechT 1).points).map
        (fun p => (p.1, (p.2 : WithTop ℝ))) :=
  dgm_points_fullComplex_eq_finite (ZMod 2) cechT (by norm_num)

/-- Item 18 identifies the empty library-triangle Rips degree-one diagram with its finite part. -/
theorem triangle_rips_dgm_one_eq_finitePart_embedding :
    (dgm (ZMod 2) ripsT 1).points =
      (finitePart (dgm (ZMod 2) ripsT 1).points).map
        (fun p => (p.1, (p.2 : WithTop ℝ))) :=
  dgm_points_fullComplex_eq_finite (ZMod 2) ripsT (by norm_num)

/-- Item 19 gives the library-triangle Čech degree-zero essential count one. -/
theorem triangle_cech_essential_card_zero_from_item19 :
    (essentialPart (dgm (ZMod 2) cechT 0).points).card = 1 :=
  Cech.card_essentialPart_dgm_zero (k := ZMod 2) Triangle.pts

/-- Item 19 gives the library-triangle Rips degree-zero essential count one. -/
theorem triangle_rips_essential_card_zero_from_item19 :
    (essentialPart (dgm (ZMod 2) ripsT 0).points).card = 1 :=
  Rips.card_essentialPart_dgm_zero (k := ZMod 2) Triangle.metric

/-! ### P2: degree-zero boundary control -/

/-- Item 19 gives one essential degree-zero bar for the two-point Rips fixture. -/
theorem twoPoints_rips_essential_card_zero_from_item19 :
    (essentialPart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points).card = 1 :=
  Rips.card_essentialPart_dgm_zero (k := ZMod 2) TwoPoints.metric

/-- The two-point essential count is strictly below the general bound `Nat.choose 2 1`. -/
theorem twoPoints_rips_essential_card_strictly_below_bound :
    1 < Nat.choose 2 1 := by
  norm_num [Nat.choose]

/-- The two-point Rips degree-one diagram has no essential bar. -/
theorem twoPoints_rips_essentialPart_one_eq_zero :
    essentialPart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 1).points = 0 :=
  Rips.essentialPart_dgm_eq_zero (k := ZMod 2) TwoPoints.metric (by norm_num)

/-- The two-point Rips degree-zero diagram has a nonempty essential part. -/
theorem twoPoints_rips_essentialPart_zero_ne_zero :
    essentialPart (dgm (ZMod 2) (Rips.filter TwoPoints.metric) 0).points ≠ 0 := by
  intro h
  have hc := twoPoints_rips_essential_card_zero_from_item19
  rw [h] at hc
  simp at hc

/-! ### P3: repeated labels -/

/-- Positive-degree repeated-label Čech diagrams vanish by item 18 and the finite-part fixture. -/
theorem repeated_cech_dgm_eq_zero_of_pos (n : ℕ) (hn : 1 ≤ n) :
    (dgm (ZMod 2) (Cech.filter Repeated.pts) n).points = 0 := by
  rw [dgm_points_fullComplex_eq_finite (ZMod 2) (Cech.filter Repeated.pts) hn,
    repeated_cech_finitePart_eq_zero n, Multiset.map_zero]

/-- Item 19 gives one essential degree-zero bar for repeated Čech labels. -/
theorem repeated_cech_essential_card_zero_from_item19 :
    (essentialPart (dgm (ZMod 2) (Cech.filter Repeated.pts) 0).points).card = 1 :=
  Cech.card_essentialPart_dgm_zero (k := ZMod 2) Repeated.pts

/-! ### P4: hollow-triangle negative control -/

/-- Every hollow-triangle face has `hollowReal` value at most one. -/
theorem hollowReal_value_le_one :
    ∀ s : TotalFace HollowTriangle.C.toPre, hollowReal.value s ≤ (1 : ℝ) := by
  intro s
  change ((s.val.card - 1 : ℕ) : ℝ) ≤ 1
  have hs := s.property
  change s.val ∈ HollowTriangle.C.faces at hs
  change s.val ∈
    ({{0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 3))) at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h | h | h | h | h <;> simp [h]

/-- Item 14 recovers rank one from the hollow-triangle essential bar. -/
theorem hollowTriangle_finrank_one_from_item14 :
    Module.finrank (ZMod 2)
        (simplicialHomology HollowTriangle.C.toPre (ZMod 2) 1) = 1 := by
  have hdiag :
      (dgm (ZMod 2) hollowReal 1).points = {((1 : ℝ), (⊤ : WithTop ℝ))} := by
    rw [← moduleDiagram_sublevelModule]
    exact hollowReal_moduleDiagram_one
  have hrank := card_essentialPart_dgm_eq_finrank
    (ZMod 2) hollowReal 1 1 hollowReal_value_le_one
  rw [hdiag] at hrank
  have hcard :
      (essentialPart ({((1 : ℝ), (⊤ : WithTop ℝ))})).card = 1 := by
    simp [essentialPart]
    rfl
  rw [hcard] at hrank
  exact hrank.symm

/-- The hollow triangle is not an apex cone at any vertex, by its item-14 rank obstruction. -/
theorem hollowTriangle_not_isApexCone :
    ∀ v, ¬ IsApexCone HollowTriangle.C.toPre v := by
  intro v hK
  have hz : IsZero (simplicialHomology HollowTriangle.C.toPre (ZMod 2) 1) :=
    hK.isZero_simplicialHomology_succ (ZMod 2) 0
  have hs : Subsingleton (simplicialHomology HollowTriangle.C.toPre (ZMod 2) 1) :=
    ModuleCat.subsingleton_of_isZero hz
  have hzero :
      Module.finrank (ZMod 2)
          (simplicialHomology HollowTriangle.C.toPre (ZMod 2) 1) = 0 := by
    haveI := hs
    exact Module.finrank_zero_of_subsingleton (R := ZMod 2)
  rw [hollowTriangle_finrank_one_from_item14] at hzero
  norm_num at hzero

/-! ### P5: filled-triangle positive control -/

/-- Every filled-triangle face has `filledReal` value at most two. -/
theorem filledReal_value_le_two :
    ∀ s : TotalFace FilledTriangle.C.toPre, filledReal.value s ≤ (2 : ℝ) := by
  intro s
  change ((s.val.card - 1 : ℕ) : ℝ) ≤ 2
  have hs := s.property
  change s.val ∈ FilledTriangle.C.faces at hs
  change s.val ∈
    ({{0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))) at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h | h | h | h | h | h <;> simp [h]

/-- Item 14 recovers rank zero from the finite filled-triangle degree-one bar. -/
theorem filledTriangle_finrank_one_from_item14 :
    Module.finrank (ZMod 2)
        (simplicialHomology FilledTriangle.C.toPre (ZMod 2) 1) = 0 := by
  have hdiag :
      (dgm (ZMod 2) filledReal 1).points = {((1 : ℝ), ((2 : ℝ) : WithTop ℝ))} := by
    rw [← moduleDiagram_sublevelModule]
    exact filledReal_moduleDiagram_one
  have hrank := card_essentialPart_dgm_eq_finrank
    (ZMod 2) filledReal 1 2 filledReal_value_le_two
  rw [hdiag] at hrank
  have hcard :
      (essentialPart ({((1 : ℝ), ((2 : ℝ) : WithTop ℝ))})).card = 0 := by
    rfl
  rw [hcard] at hrank
  exact hrank.symm

/-- Item 11 independently gives rank zero after transporting the filled complex to the top complex. -/
theorem filledTriangle_finrank_one_from_fullComplex :
    Module.finrank (ZMod 2)
        (simplicialHomology FilledTriangle.C.toPre (ZMod 2) 1) = 0 := by
  rw [filledTriangle_toPre_eq]
  have hz :
      IsZero (simplicialHomology (Rips.fullComplex (Fin 3)) (ZMod 2) 1) :=
    TDA.Simplicial.isZero_simplicialHomology_top_succ (V := Fin 3) (ZMod 2) 0
  have hs :
      Subsingleton
        (simplicialHomology (Rips.fullComplex (Fin 3)) (ZMod 2) 1) :=
    ModuleCat.subsingleton_of_isZero hz
  haveI := hs
  exact Module.finrank_zero_of_subsingleton (R := ZMod 2)

/-! ### P6: size-uniform Čech consumers -/

/-- The degree-one Čech image bound for the triangle has the simplified count factor two. -/
theorem triangle_cech_finiteDiagramImage_size_uniform
    (q : Fin 3 → EuclideanSpace ℝ (Fin 2))
    {K : Type*} [Fintype K] {σ A B : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P
          (dgm (ZMod 2) (Cech.filter Triangle.pts) 1) -
        PersistenceImage.finiteDiagramImage σ w P
          (dgm (ZMod 2) (Cech.filter q) 1)‖ ≤
      PersistenceImage.stabilityConstant σ A B * 2 * Cech.displacement Triangle.pts q := by
  have h := Cech.norm_finiteDiagramImage_sub_le_choose_mul_displacement
    (k := ZMod 2) Triangle.pts q 1 hσ hA hB w P hm hd
  norm_num [Nat.choose] at h
  exact h

/-- The same size-uniform Čech consumer typechecks with the arctangent weight and constant. -/
theorem triangle_cech_finiteDiagramImage_arctan_size_uniform
    (q : Fin 3 → EuclideanSpace ℝ (Fin 2))
    {K : Type*} [Fintype K] {σ C : ℝ}
    (hσ : 0 < σ) (hC : 0 ≤ C) (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight C hC) P
          (dgm (ZMod 2) (Cech.filter Triangle.pts) 1) -
        PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight C hC) P
          (dgm (ZMod 2) (Cech.filter q) 1)‖ ≤
      (2 * C + 3 * √(π / 2) / σ) * 2 * Cech.displacement Triangle.pts q := by
  have h := Cech.norm_finiteDiagramImage_sub_le_choose_mul_displacement
    (k := ZMod 2) Triangle.pts q 1 (σ := σ) (A := C) (B := π / 2) hσ hC
      Real.pi_div_two_pos.le (PersistenceImage.arctanWeight C hC) P hm hd
  norm_num [Nat.choose] at h
  simpa only [PersistenceImage.stabilityConstant_arctan] using h

/-! ### P6: weighted-kernel consumer -/

/-- The degree-one Čech weighted-kernel bound for the triangle has count factor two. -/
theorem triangle_cech_diagramEmbedding_arctan_size_uniform
    (q : Fin 3 → EuclideanSpace ℝ (Fin 2))
    {σ C : ℝ} (hC : 0 ≤ C) :
    ‖WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (dgm (ZMod 2) (Cech.filter Triangle.pts) 1) -
        WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (dgm (ZMod 2) (Cech.filter q) 1)‖ ≤
      (2 * C + √2 * π / (2 * |σ|)) * 2 * Cech.displacement Triangle.pts q := by
  have h := Cech.norm_diagramEmbedding_sub_le_choose_mul_displacement
    (k := ZMod 2) Triangle.pts q 1 σ (A := C) (B := π / 2) hC
      Real.pi_div_two_pos.le (PersistenceImage.arctanWeight C hC)
  norm_num [Nat.choose] at h
  simpa only [WeightedKernel.stabilityConstant_arctan] using h

end

end TDA.Persistence.EssentialVanishingExamples
