import TDA.Probability.FiniteSampling

/-!
# Total variation and maximal couplings of finite probability laws

The normalization is the probability of a mismatch under a maximal coupling,
which is one half of the finite L¹ distance. Zero-weight atoms are allowed.
-/

noncomputable section

universe u
namespace TDA.Probability

open scoped ENNReal Classical

variable {X : Type u} [Fintype X]

/-- Finite total variation, normalized to lie in the unit interval. -/
def finiteTotalVariation (μ ν : PMF X) : ℝ≥0∞ :=
  ∑ x, (μ x - min (μ x) (ν x))

/-- The mass shared by two finite probability laws. -/
def finiteCommonMass (μ ν : PMF X) : ℝ≥0∞ :=
  ∑ x, min (μ x) (ν x)

private theorem sum_pmf (μ : PMF X) : ∑ x, μ x = 1 := by
  simpa only [tsum_fintype] using μ.tsum_coe

/-- Total variation is also the sum of the positive mass differences. -/
theorem finiteTotalVariation_eq_sum_sub (μ ν : PMF X) :
    finiteTotalVariation μ ν = ∑ x, (μ x - ν x) := by
  simp only [finiteTotalVariation, tsub_min]

/-- The residual mass and the common mass sum to one. -/
theorem finiteTotalVariation_add_commonMass (μ ν : PMF X) :
    finiteTotalVariation μ ν + finiteCommonMass μ ν = 1 := by
  rw [finiteTotalVariation_eq_sum_sub, finiteCommonMass, ← Finset.sum_add_distrib]
  simpa only [tsub_add_min] using sum_pmf μ

/-- Finite total variation never exceeds one. -/
theorem finiteTotalVariation_le_one (μ ν : PMF X) : finiteTotalVariation μ ν ≤ 1 := by
  calc
    _ ≤ finiteTotalVariation μ ν + finiteCommonMass μ ν := le_self_add
    _ = 1 := finiteTotalVariation_add_commonMass μ ν

/-- The shared mass never exceeds one. -/
theorem finiteCommonMass_le_one (μ ν : PMF X) : finiteCommonMass μ ν ≤ 1 := by
  calc
    _ ≤ finiteTotalVariation μ ν + finiteCommonMass μ ν := le_add_self
    _ = 1 := finiteTotalVariation_add_commonMass μ ν

/-- Total variation is one minus the common mass. -/
theorem finiteTotalVariation_eq_one_sub_commonMass (μ ν : PMF X) :
    finiteTotalVariation μ ν = 1 - finiteCommonMass μ ν :=
  ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (finiteTotalVariation_add_commonMass μ ν)

/-- Finite total variation is symmetric. -/
theorem finiteTotalVariation_comm (μ ν : PMF X) :
    finiteTotalVariation μ ν = finiteTotalVariation ν μ := by
  simp only [finiteTotalVariation_eq_one_sub_commonMass, finiteCommonMass, min_comm]

/-- Vanishing total variation is exactly equality of probability laws. -/
@[simp] theorem finiteTotalVariation_eq_zero_iff (μ ν : PMF X) :
    finiteTotalVariation μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    have h' : ∀ x, μ x ≤ ν x := by
      intro x
      have hx : μ x - ν x = 0 := by
        apply le_antisymm _ bot_le
        calc
          _ ≤ ∑ y, (μ y - ν y) := Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ x)
          _ = 0 := (finiteTotalVariation_eq_sum_sub μ ν).symm.trans h
      exact tsub_eq_zero_iff_le.mp hx
    have hrev : finiteTotalVariation ν μ = 0 := (finiteTotalVariation_comm ν μ).trans h
    have h'' : ∀ x, ν x ≤ μ x := by
      intro x
      apply tsub_eq_zero_iff_le.mp
      apply le_antisymm _ bot_le
      calc
        _ ≤ ∑ y, (ν y - μ y) := Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ x)
        _ = 0 := (finiteTotalVariation_eq_sum_sub ν μ).symm.trans hrev
    exact PMF.ext (fun x => le_antisymm (h' x) (h'' x))
  · rintro rfl
    simp [finiteTotalVariation]

/-- A law has zero total variation from itself. -/
@[simp] theorem finiteTotalVariation_self (μ : PMF X) : finiteTotalVariation μ μ = 0 :=
  (finiteTotalVariation_eq_zero_iff μ μ).mpr rfl

/-- Twice total variation is the finite L¹ difference of the atom masses. -/
theorem two_mul_finiteTotalVariation_eq_sum_abs (μ ν : PMF X) :
    2 * finiteTotalVariation μ ν =
      ∑ x, ENNReal.ofReal |(μ x).toReal - (ν x).toReal| := by
  have hpoint (x : X) : ENNReal.ofReal |(μ x).toReal - (ν x).toReal| =
      (μ x - ν x) + (ν x - μ x) := by
    rcases le_total (μ x) (ν x) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr (ENNReal.toReal_mono (ν.apply_ne_top x) h)),
        neg_sub, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
      simp [ENNReal.ofReal_toReal, μ.apply_ne_top x, ν.apply_ne_top x,
        tsub_eq_zero_of_le h]
    · rw [abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono (μ.apply_ne_top x) h)),
        ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
      simp [ENNReal.ofReal_toReal, μ.apply_ne_top x, ν.apply_ne_top x,
        tsub_eq_zero_of_le h]
  simp only [hpoint, Finset.sum_add_distrib, ← finiteTotalVariation_eq_sum_sub,
    ← finiteTotalVariation_comm μ ν, two_mul]

/-- The conventional finite half-L¹ formula for total variation. -/
theorem finiteTotalVariation_eq_half_sum_abs (μ ν : PMF X) :
    finiteTotalVariation μ ν = (2 : ℝ≥0∞)⁻¹ *
      ∑ x, ENNReal.ofReal |(μ x).toReal - (ν x).toReal| := by
  rw [← two_mul_finiteTotalVariation_eq_sum_abs]
  rw [ENNReal.inv_mul_cancel_left (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]

/-- Diagonal coupling of a law with itself. -/
def Coupling.diagonal (μ : PMF X) : Coupling μ μ where
  joint := μ.map (fun x => (x, x))
  fst_map := by rw [PMF.map_comp]; exact PMF.map_id μ
  snd_map := by rw [PMF.map_comp]; exact PMF.map_id μ

open scoped Classical in
private def maximalMass (μ ν : PMF X) (x y : X) : ℝ≥0∞ :=
  (if x = y then min (μ x) (ν x) else 0) +
    (μ x - ν x) * (ν y - μ y) * (finiteTotalVariation μ ν)⁻¹

private theorem sum_maximalMass_row (μ ν : PMF X)
    (hδ : finiteTotalVariation μ ν ≠ 0) (x : X) :
    ∑ y, maximalMass μ ν x y = μ x := by
  classical
  have hδtop : finiteTotalVariation μ ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (finiteTotalVariation_le_one μ ν)
  simp only [maximalMass, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, ← finiteTotalVariation_eq_sum_sub, ← finiteTotalVariation_comm μ ν]
  rw [ENNReal.mul_inv_cancel_right hδ hδtop]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (add_comm _ _).trans tsub_add_min

private theorem sum_maximalMass_col (μ ν : PMF X)
    (hδ : finiteTotalVariation μ ν ≠ 0) (y : X) :
    ∑ x, maximalMass μ ν x y = ν y := by
  classical
  have hδtop : finiteTotalVariation μ ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (finiteTotalVariation_le_one μ ν)
  simp only [maximalMass, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← finiteTotalVariation_eq_sum_sub]
  rw [mul_comm (finiteTotalVariation μ ν) (ν y - μ y),
    ENNReal.mul_inv_cancel_right hδ hδtop]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [min_comm]
  exact (add_comm _ _).trans tsub_add_min

private def maximalCouplingNonzero (μ ν : PMF X)
    (hδ : finiteTotalVariation μ ν ≠ 0) : Coupling μ ν where
  joint := PMF.ofFintype (fun xy => maximalMass μ ν xy.1 xy.2) (by
    rw [Fintype.sum_prod_type]
    simp only [sum_maximalMass_row μ ν hδ]
    exact sum_pmf μ)
  fst_map := by
    classical
    ext x
    simp only [PMF.map_apply, PMF.ofFintype_apply, tsum_fintype, Fintype.sum_prod_type]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact sum_maximalMass_row μ ν hδ x
  snd_map := by
    classical
    ext y
    simp only [PMF.map_apply, PMF.ofFintype_apply, tsum_fintype, Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact sum_maximalMass_col μ ν hδ y

/-- An explicit maximal coupling: preserve common diagonal mass, and couple
residual marginals independently. The zero-distance branch is diagonal. -/
def maximalCoupling (μ ν : PMF X) : Coupling μ ν := by
  classical
  by_cases hδ : finiteTotalVariation μ ν = 0
  · have h := (finiteTotalVariation_eq_zero_iff μ ν).mp hδ
    subst ν
    exact Coupling.diagonal μ
  · exact maximalCouplingNonzero μ ν hδ

/-- Atom formula for the explicit maximal coupling. The residual product has
zero diagonal, and is normalized by the common residual mass. -/
theorem maximalCoupling_joint_apply (μ ν : PMF X) (x y : X) :
    (maximalCoupling μ ν).joint (x, y) =
      (if x = y then min (μ x) (ν x) else 0) +
        (μ x - ν x) * (ν y - μ y) * (finiteTotalVariation μ ν)⁻¹ := by
  classical
  by_cases hδ : finiteTotalVariation μ ν = 0
  · have h := (finiteTotalVariation_eq_zero_iff μ ν).mp hδ
    subst ν
    by_cases hxy : x = y
    · subst y
      simp [maximalCoupling, Coupling.diagonal, PMF.map_apply]
    · simp [maximalCoupling, Coupling.diagonal, PMF.map_apply, hxy, Ne.symm hxy,
        Prod.mk.injEq]
  · simp [maximalCoupling, hδ, maximalCouplingNonzero, maximalMass]

/-- The maximal coupling preserves exactly the shared mass at each diagonal atom. -/
@[simp] theorem maximalCoupling_joint_diagonal (μ ν : PMF X) (x : X) :
    (maximalCoupling μ ν).joint (x, x) = min (μ x) (ν x) := by
  rw [maximalCoupling_joint_apply]
  rcases le_total (μ x) (ν x) with h | h <;>
    simp [tsub_eq_zero_of_le h]

/-- The mismatch probability of the constructed coupling is total variation. -/
theorem maximalCoupling_mismatch (μ ν : PMF X) :
    expectation (maximalCoupling μ ν).joint
      (fun xy => if xy.1 = xy.2 then 0 else 1) = finiteTotalVariation μ ν := by
  classical
  let π := maximalCoupling μ ν
  have hdiag : (∑ xy : X × X, if xy.1 = xy.2 then π.joint xy else 0) =
      finiteCommonMass μ ν := by
    rw [Fintype.sum_prod_type]
    simp [π, finiteCommonMass]
  have hmass : expectation π.joint (fun xy => if xy.1 = xy.2 then 0 else 1) +
      finiteCommonMass μ ν = 1 := by
    rw [← hdiag, expectation, tsum_fintype, ← Finset.sum_add_distrib]
    convert sum_pmf π.joint using 1
    apply Finset.sum_congr rfl
    intro xy _
    by_cases h : xy.1 = xy.2 <;> simp [h]
  exact (ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top hmass).trans
    (finiteTotalVariation_eq_one_sub_commonMass μ ν).symm

end TDA.Probability
