import TDA.Persistence.RipsSampling
import TDA.Persistence.RipsGromovHausdorffExamples
import TDA.Persistence.EssentialVanishing
import Mathlib.Data.ZMod.Basic

/-! Concrete atomic examples of sampled Rips laws and the vanishing-mass input. -/

noncomputable section
namespace TDA.Persistence.RipsSamplingExamples

open TDA.Probability TDA.Persistence.Rips
open scoped ENNReal NNReal

/-- The two nonnegative masses are allowed to reach zero at either endpoint. -/
def twoPointWeights (ε : ℝ≥0) (hε : ε ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ((if b then ε else 1 - ε : ℝ≥0) : ℝ≥0∞)) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le hε]
    rfl)

/-- Points at distance one, with masses `1-ε` and `ε`. -/
def twoPointLaw (ε : ℝ≥0) (hε : ε ≤ 1) : PMF ℝ :=
  (twoPointWeights ε hε).map (fun b => if b then (1 : ℝ) else 0)

/-- The two-draw moment is `2ε(1-ε)` for every positive exponent. Thus the
whole-support diagram cannot replace the sampled diagram law in a GW estimate. -/
theorem twoPoint_gromovWasserstein_singleton (ε : ℝ≥0) (hε : ε ≤ 1)
    {p : ℝ} (hp : 0 < p) :
    gromovWasserstein p (twoPointLaw ε hε) (PMF.pure (() : Unit)) =
      (2 : ℝ≥0∞)⁻¹ * (2 * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞)) ^ p⁻¹ := by
  rw [gromovWasserstein_of_subsingleton]
  simp only [twoPointLaw, expectation_map]
  congr 2
  simp [expectation, tsum_fintype, Fintype.sum_bool, twoPointWeights, PMF.ofFintype_apply,
    Real.dist_eq, ENNReal.zero_rpow_of_pos hp, mul_comm, mul_left_comm, mul_assoc]
  ring

/-- The sharp law theorem applies to this weighted nonuniform input, with a
one-point target, in positive degree and with iid replacement. -/
theorem weighted_twoPoint_sampleLaw_bound (ε : ℝ≥0) (hε : ε ≤ 1)
    {p : ℝ} (hp : 1 ≤ p) (n degree : ℕ) (hn : 2 ≤ n) :
    wasserstein p bottleneck
      (sampleLaw (ZMod 2) (twoPointLaw ε hε) n (degree + 1))
      (sampleLaw (ZMod 2) (PMF.pure (() : Unit)) n (degree + 1)) ≤
      (n.choose 2 : ℝ≥0∞) ^ p⁻¹ *
        (2 * gromovWasserstein p (twoPointLaw ε hε)
          (PMF.pure (() : Unit))) :=
  wasserstein_sampleLaw_le_gromovWasserstein (ZMod 2)
    (twoPointLaw ε hε) (PMF.pure (() : Unit)) hp n degree hn

section NontrivialLaw

open TDA.Persistence.Rips.GromovHausdorffExamples
open TDA.Persistence TDA.Filtration

local instance : MetricSpace (Fin 2) := TDA.Filtration.Cech.Examples.TwoPoints.metric
local instance : MetricSpace (Fin 1) :=
  MetricSpace.induced (fun _ : Fin 1 => (0 : ℝ))
    (fun a b _ => Subsingleton.elim a b) inferInstance

/-- Equal positive masses on the two points at distance two. -/
def uniformTwoPoints : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => (2 : ℝ≥0∞)⁻¹) (by
    simp only [Fin.sum_univ_two, ← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- The ordered two-draw tuple visiting both points. -/
def distinctDraws : Fin 2 → Fin 2 := Fin.cons 0 (Fin.cons 1 Fin.elim0)

/-- Two different draws retain both the essential H₀ occurrence and the
finite bar dying at the edge's diameter time. -/
theorem distinctDraws_fullH0_points :
    (sampleDiagram (ZMod 2) distinctDraws 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), (0, ((2 : ℝ) : WithTop ℝ))} := by
  rw [sampleDiagram_eq_diagram_of_surjective (ZMod 2) distinctDraws (by
    intro i
    fin_cases i <;> simp [distinctDraws]) 0]
  exact two_points_diagram

/-- A one-point Rips sample has exactly its essential H₀ occurrence. -/
theorem singleton_fullH0_points :
    (diagram (ZMod 2) (Fin 1) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  rw [diagram_eq_dgm]
  let d : MetricSpace (Fin 1) := inferInstance
  let D := dgm (ZMod 2) (Rips.filter d) 0
  have hd0 : Rips.diameter d (Finset.univ : Finset (Fin 1)) = 0 := by
    rw [show (Finset.univ : Finset (Fin 1)) = {0} by decide]
    exact Rips.diameter_singleton d 0
  have hfin : finitePart D.points = 0 := by
    have h := card_finiteOccurrences_dgm_fullComplex_le (ZMod 2) (Rips.filter d) 0
    apply Multiset.card_eq_zero.mp
    have hc : Fintype.card D.finiteOccurrences = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [D] using h
    simpa only [Multiset.card_coe] using hc
  have hess : essentialPart D.points = {0} := by
    have hc := Rips.card_essentialPart_dgm_zero (ZMod 2) d
    obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hc
    have hbmem : b ∈ essentialPart D.points := by rw [hb]; simp
    have hbounds := (Rips.dgm_coordinates_le_diameter (ZMod 2) d 0).2 b hbmem
    have hb0 : b = 0 := by linarith [hd0]
    simpa [hb0] using hb
  have h := parts_reconstruct D.points
  simpa only [hfin, hess, Multiset.map_zero, Multiset.map_singleton, zero_add] using h.symm

/-- Two equal ordered draws, parameterized by the point drawn. -/
def repeatedDraws (b : Fin 2) : Fin 2 → Fin 2 := fun _ => b

/-- Repetition collapses to a one-point metric sample. -/
theorem repeatedDraws_diagram_eq_singleton (b : Fin 2) :
    sampleDiagram (ZMod 2) (repeatedDraws b) 0 = diagram (ZMod 2) (Fin 1) 0 := by
  let t : Fin 2 → Fin 2 := repeatedDraws b
  letI : Subsingleton (Sample t) := ⟨by
    intro a c
    apply Subtype.ext
    rcases a.property with ⟨i, hi⟩
    rcases c.property with ⟨j, hj⟩
    simpa [t, repeatedDraws] using hi.symm.trans hj⟩
  let e : Sample t ≃ᵢ Fin 1 :=
    { Equiv.ofBijective (fun _ : Sample t => (0 : Fin 1))
        ⟨fun a c _ => Subsingleton.elim a c,
         fun y => ⟨sampleProjection t 0, Subsingleton.elim _ y⟩⟩ with
      isometry_toFun := by
        intro a c
        have hac : a = c := Subsingleton.elim a c
        subst c
        simp }
  exact diagram_eq_of_isometryEquiv (ZMod 2) e 0

/-- Equal draws retain the sole essential H₀ occurrence. -/
theorem repeatedDraws_fullH0_points (b : Fin 2) :
    (sampleDiagram (ZMod 2) (repeatedDraws b) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ))} := by
  rw [repeatedDraws_diagram_eq_singleton b]
  exact singleton_fullH0_points

private theorem mass_ge_half_of_two_orders (D : Diagram ℝ) (y₀ y₁ : Fin 2)
    (h₀ : sampleDiagram (ZMod 2)
      (Fin.cons (0 : Fin 2) (Fin.cons y₀ Fin.elim0)) 0 = D)
    (h₁ : sampleDiagram (ZMod 2)
      (Fin.cons (1 : Fin 2) (Fin.cons y₁ Fin.elim0)) 0 = D) :
    (2 : ℝ≥0∞)⁻¹ ≤ (sampleLaw (ZMod 2) uniformTwoPoints 2 0) D := by
  classical
  have hmass : expectation (sampleLaw (ZMod 2) uniformTwoPoints 2 0)
      (fun E => if E = D then 1 else 0) =
      (sampleLaw (ZMod 2) uniformTwoPoints 2 0) D := by
    simp [expectation]
  rw [← hmass]
  unfold sampleLaw
  rw [expectation_map]
  rw [iid_succ, expectation_bind]
  simp only [expectation_map, iid_succ, expectation_bind, iid_zero, expectation_pure]
  unfold expectation
  simp only [tsum_fintype]
  rw [Fin.sum_univ_two]
  calc
    (2 : ℝ≥0∞)⁻¹ = uniformTwoPoints 0 * (uniformTwoPoints y₀ *
        if (sampleDiagram (ZMod 2)
          (Fin.cons (0 : Fin 2) (Fin.cons y₀ Fin.elim0)) 0) = D
          then 1 else 0) + uniformTwoPoints 1 * (uniformTwoPoints y₁ *
        if (sampleDiagram (ZMod 2)
          (Fin.cons (1 : Fin 2) (Fin.cons y₁ Fin.elim0)) 0) = D
          then 1 else 0) := by
      simp only [h₀, h₁, ↓reduceIte, mul_one, uniformTwoPoints, PMF.ofFintype_apply]
      calc
        (2 : ℝ≥0∞)⁻¹ = 2 * (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          simp
        _ = (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ +
            (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by ring
    _ ≤ uniformTwoPoints 0 * (∑ x_1 : Fin 2, uniformTwoPoints x_1 *
        if (sampleDiagram (ZMod 2)
          (Fin.cons (0 : Fin 2) (Fin.cons x_1 Fin.elim0)) 0) = D
          then 1 else 0) + uniformTwoPoints 1 * (∑ x_1 : Fin 2, uniformTwoPoints x_1 *
        if (sampleDiagram (ZMod 2)
          (Fin.cons (1 : Fin 2) (Fin.cons x_1 Fin.elim0)) 0) = D
          then 1 else 0) := by
      gcongr
      · simpa only [tsum_fintype] using (ENNReal.le_tsum (f := fun x_1 : Fin 2 =>
          uniformTwoPoints x_1 * if (sampleDiagram (ZMod 2)
            (Fin.cons (0 : Fin 2) (Fin.cons x_1 Fin.elim0)) 0) = D
            then 1 else 0) y₀)
      · simpa only [tsum_fintype] using (ENNReal.le_tsum (f := fun x_1 : Fin 2 =>
          uniformTwoPoints x_1 * if (sampleDiagram (ZMod 2)
            (Fin.cons (1 : Fin 2) (Fin.cons x_1 Fin.elim0)) 0) = D
            then 1 else 0) y₁)

/-- At least half of the two-draw law is concentrated at the nontrivial full
H₀ diagram. The two orders of the distinct draws each contribute one quarter. -/
theorem uniformTwoPoints_nontrivial_fullH0_mass :
    (2 : ℝ≥0∞)⁻¹ ≤
      (sampleLaw (ZMod 2) uniformTwoPoints 2 0) (diagram (ZMod 2) (Fin 2) 0) := by
  apply mass_ge_half_of_two_orders _ 1 0
  · change sampleDiagram (ZMod 2) distinctDraws 0 = _
    exact sampleDiagram_eq_diagram_of_surjective (ZMod 2) distinctDraws (by
      intro i
      fin_cases i <;> simp [distinctDraws]) 0
  · exact sampleDiagram_eq_diagram_of_surjective (ZMod 2)
      (Fin.cons (1 : Fin 2) (Fin.cons 0 Fin.elim0)) (by
        intro i
        fin_cases i <;> simp) 0

/-- The other two ordered outcomes both have the singleton diagram, also with
probability at least one half. -/
theorem uniformTwoPoints_singleton_fullH0_mass :
    (2 : ℝ≥0∞)⁻¹ ≤
      (sampleLaw (ZMod 2) uniformTwoPoints 2 0) (diagram (ZMod 2) (Fin 1) 0) := by
  apply mass_ge_half_of_two_orders _ 0 1
  · have ht : (Fin.cons (0 : Fin 2) (Fin.cons 0 Fin.elim0) : Fin 2 → Fin 2) =
        repeatedDraws 0 := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg (fun t : Fin 2 → Fin 2 => sampleDiagram (ZMod 2) t 0) ht).trans
      (repeatedDraws_diagram_eq_singleton 0)
  · have ht : (Fin.cons (1 : Fin 2) (Fin.cons 1 Fin.elim0) : Fin 2 → Fin 2) =
        repeatedDraws 1 := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg (fun t : Fin 2 → Fin 2 => sampleDiagram (ZMod 2) t 0) ht).trans
      (repeatedDraws_diagram_eq_singleton 1)

/-- The two sampled full H₀ diagrams have different occurrence counts. -/
theorem distinctDraws_ne_repeatedDraws :
    sampleDiagram (ZMod 2) distinctDraws 0 ≠
      sampleDiagram (ZMod 2) (repeatedDraws 0) 0 := by
  intro h
  have hc := congrArg (fun D : Diagram ℝ => D.points.card) h
  rw [distinctDraws_fullH0_points, repeatedDraws_fullH0_points] at hc
  norm_num at hc

/-- The iid two-point H₀ sample law has two distinct atoms of positive mass. -/
theorem uniformTwoPoints_sampleLaw_nonconstant :
    ∃ D E : Diagram ℝ, D ≠ E ∧
      0 < (sampleLaw (ZMod 2) uniformTwoPoints 2 0) D ∧
      0 < (sampleLaw (ZMod 2) uniformTwoPoints 2 0) E := by
  refine ⟨diagram (ZMod 2) (Fin 2) 0, diagram (ZMod 2) (Fin 1) 0, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun D : Diagram ℝ => D.points.card) h
    rw [two_points_diagram, singleton_fullH0_points] at hc
    norm_num at hc
  · exact lt_of_lt_of_le (by norm_num) uniformTwoPoints_nontrivial_fullH0_mass
  · exact lt_of_lt_of_le (by norm_num) uniformTwoPoints_singleton_fullH0_mass

end NontrivialLaw

end TDA.Persistence.RipsSamplingExamples
