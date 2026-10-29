import TDA.Persistence.PersistenceMeasureEssential
import TDA.Persistence.RealIntervalInterleaving
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Rectangle boundaries and the essential boundary

These fixtures use the existing real interval module. An interval born at the upper
birth edge and dying at the upper death edge contributes once. Moving its birth to
the lower edge removes that contribution. An essential interval has no finite-death
rectangle mass but retains one occurrence on the essential boundary.
-/

universe u

namespace TDA.Persistence.PersistenceMeasureExamples

open CategoryTheory
open scoped Classical

variable {k : Type u} [Field k]

private noncomputable def ephemeralModule : PModule.{u,0,u} k ℝ where
  obj _ := ModuleCat.of k (ℕ →₀ k)
  map {s t} _ := if s = t then 𝟙 (ModuleCat.of k (ℕ →₀ k)) else 0
  map_id _ := by simp
  map_comp {s t r} f g := by
    have hst : s ≤ t := leOfHom f
    have htr : t ≤ r := leOfHom g
    by_cases h : s = t
    · subst t
      simp
    · by_cases h' : t = r
      · subst r
        simp [h]
      · have hsr : s ≠ r := by
          intro heq
          subst r
          exact h (le_antisymm hst htr)
        simp [h, h', hsr]

private theorem ephemeral_strict_map {a b : ℝ} (hab : a < b) :
    structureMapLinear (ephemeralModule (k := k)) hab.le = 0 := by
  simp only [structureMapLinear, structureMap, ephemeralModule, if_neg hab.ne]
  rfl

/-- Infinite-dimensional fibers can be entirely ephemeral and still be q-tame. -/
theorem infinite_ephemeral_qTame : (ephemeralModule (k := k)).QTame := by
  intro a b hab
  rw [ephemeral_strict_map hab]
  change FiniteDimensional k (LinearMap.range (0 : (ℕ →₀ k) →ₗ[k] (ℕ →₀ k)))
  rw [LinearMap.range_zero]
  infer_instance

/-- The ephemeral fixture really has infinite-dimensional fibers. -/
theorem infinite_ephemeral_not_finiteDimensional (t : ℝ) :
    ¬ FiniteDimensional k ((ephemeralModule (k := k)).obj t) := by
  intro h
  have : FiniteDimensional k (ℕ →₀ k) := h
  let := FiniteDimensional.fintypeBasisIndex
    (Finsupp.basisSingleOne : Module.Basis ℕ k (ℕ →₀ k))
  exact not_finite ℕ

/-- Separated rectangles discard diagonal ephemeral information. -/
theorem infinite_ephemeral_rectangle_zero {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) :
    persistenceMeasureValue (ephemeralModule (k := k)) hab hbc.le hcd = 0 :=
  persistenceMeasureValue_eq_zero_of_crossing_eq_zero _ _ _ _ (ephemeral_strict_map hbc)

private theorem intervalImage_rank (p : ℝ × WithTop ℝ) {s t : ℝ} (hst : s ≤ t) :
    Module.finrank k (persistenceImage (RealBarcode.intervalModule (k := k) p) hst) =
      if RealBarcode.alive p s ∧ RealBarcode.alive p t then 1 else 0 := by
  classical
  let f := structureMapLinear (RealBarcode.intervalModule (k := k) p) hst
  by_cases h : RealBarcode.alive p s ∧ RealBarcode.alive p t
  · rw [if_pos h]
    have hf : Function.Surjective f := by
      intro y
      let x : RealBarcode.fiber (k := k) p s :=
        ⟨y.val, by simp [RealBarcode.fiber, h.1]⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      simpa [f, structureMapLinear, structureMap, h.2] using
        RealBarcode.map_val p (homOfLE hst) x
    change Module.finrank k (LinearMap.range f) = 1
    rw [LinearMap.range_eq_top.mpr hf, finrank_top]
    change Module.finrank k (RealBarcode.fiber (k := k) p t) = 1
    rw [show RealBarcode.fiber (k := k) p t = ⊤ by
      unfold RealBarcode.fiber
      exact if_pos h.2]
    rw [finrank_top]
    exact Module.finrank_self k
  · rw [if_neg h]
    have hf : f = 0 := by
      ext x
      apply Subtype.ext
      change (f x).val = 0
      have hv : (f x).val = if RealBarcode.alive p t then x.val else 0 :=
        RealBarcode.map_val p (homOfLE hst) x
      rw [hv]
      by_cases ht : RealBarcode.alive p t
      · rw [if_pos ht]
        have hs : ¬ RealBarcode.alive p s := fun hs => h ⟨hs, ht⟩
        have hx : (show RealBarcode.fiber (k := k) p s from x).val = 0 := by
          simpa only [RealBarcode.fiber, if_neg hs, Submodule.mem_bot] using
            (show RealBarcode.fiber (k := k) p s from x).property
        exact hx
      · rw [if_neg ht]
    change Module.finrank k (LinearMap.range f) = 0
    rw [hf, LinearMap.range_zero]
    exact finrank_bot k _

private instance intervalImage_finiteDimensional (p : ℝ × WithTop ℝ)
    {s t : ℝ} (hst : s ≤ t) :
    FiniteDimensional k (persistenceImage (RealBarcode.intervalModule (k := k) p) hst) := by
  have : FiniteDimensional k ((RealBarcode.intervalModule (k := k) p).obj s) := by
    change FiniteDimensional k (RealBarcode.fiber (k := k) p s)
    infer_instance
  exact LinearMap.finiteDimensional_range _

/-- The closed birth and excluded death of `[0,2)` are counted on the upper edges. -/
theorem upper_edges_count_one :
    persistenceMeasureValue (RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ)))
      (show (-1 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) ≤ 2 by norm_num) = 1 := by
  have h := persistenceMeasureValue_four_rank
    (RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ)))
    (show (-1 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
    (show (1 : ℝ) ≤ 2 by norm_num)
  simp only [intervalImage_rank] at h
  norm_num [RealBarcode.alive] at h
  exact_mod_cast h

/-- An interval already alive on the lower birth edge is excluded. -/
theorem lower_birth_edge_count_zero :
    persistenceMeasureValue (RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ)))
      (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      (show (3 / 2 : ℝ) ≤ 2 by norm_num) = 0 := by
  have h := persistenceMeasureValue_four_rank
    (RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ)))
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    (show (3 / 2 : ℝ) ≤ 2 by norm_num)
  simp only [intervalImage_rank] at h
  norm_num [RealBarcode.alive] at h
  exact_mod_cast h

/-- An essential interval contributes to no finite-death rectangle. -/
theorem essential_interval_finite_rectangle_zero {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    persistenceMeasureValue (RealBarcode.intervalModule (k := k) (0, ⊤)) hab hbc hcd = 0 := by
  have h := persistenceMeasureValue_four_rank
    (RealBarcode.intervalModule (k := k) (0, ⊤)) hab hbc hcd
  simp only [intervalImage_rank, RealBarcode.alive, WithTop.coe_lt_top, and_true] at h
  have h₁ : (0 ≤ b ∧ 0 ≤ c) ↔ 0 ≤ b :=
    ⟨And.left, fun hb => ⟨hb, hb.trans hbc⟩⟩
  have h₂ : (0 ≤ a ∧ 0 ≤ c) ↔ 0 ≤ a :=
    ⟨And.left, fun ha => ⟨ha, (ha.trans hab).trans hbc⟩⟩
  have h₃ : (0 ≤ b ∧ 0 ≤ d) ↔ 0 ≤ b :=
    ⟨And.left, fun hb => ⟨hb, (hb.trans hbc).trans hcd⟩⟩
  have h₄ : (0 ≤ a ∧ 0 ≤ d) ↔ 0 ≤ a :=
    ⟨And.left, fun ha => ⟨ha, ((ha.trans hab).trans hbc).trans hcd⟩⟩
  simp only [h₁, h₂, h₃, h₄] at h
  omega

/-- The essential interval has one occurrence on the death-at-infinity boundary. -/
theorem essential_interval_count_one :
    essentialMeasureValue (RealBarcode.intervalModule (k := k) (0, ⊤))
      (show (-1 : ℝ) ≤ 0 by norm_num) = 1 := by
  obtain ⟨c, hc, h⟩ := exists_tail_eq_essentialMeasureValue
    (RealBarcode.intervalModule (k := k) (0, ⊤)) (show (-1 : ℝ) ≤ 0 by norm_num)
  have ht := persistenceTailMeasureValue_add_image
    (RealBarcode.intervalModule (k := k) (0, ⊤))
    (show (-1 : ℝ) ≤ 0 by norm_num) hc.le
  simp only [intervalImage_rank] at ht
  norm_num [RealBarcode.alive, hc.le] at ht
  omega

end TDA.Persistence.PersistenceMeasureExamples
