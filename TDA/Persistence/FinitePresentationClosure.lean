import TDA.Persistence.FinitePresentationHomShift
import TDA.Persistence.CoordinateInterleavingLowering
import TDA.Persistence.CoordinateInterleavingDistance
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Attainment and separation for finitely presented multiparameter modules

Finite presentations give a uniform positive right slack for the four Hom sets
that enter the two interleaving equations. Lifting both maps through that slack
and cancelling after the double shift removes a small parameter increase.
The infimum defining the interleaving distance is therefore attained whenever
it is finite, and distance zero characterizes natural isomorphism.

This proves the finite-presentation closure argument of Lesnick's Theorem 6.1
(arXiv:1106.5305v4) from actual finite generators and relations. The coefficient
ring need not be a field, and the coordinate dimension may be zero.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.GradedFree

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal ENNReal

variable {R : Type u} [Ring R] {n : ℕ}
variable {M N : PModule.{u,0,max u w} R (Fin n → ℝ)}

private theorem injective_postcomp_shiftLE_congr
    (M : PModule.{u,0,max u w} R (Fin n → ℝ))
    {ε δ σ : ℝ≥0} (hεδ : ε ≤ δ) (hεσ : ε ≤ σ) (hδσ : δ = σ)
    (h : Function.Injective (fun f : M ⟶ (shift ε).obj M => f ≫ shiftLE hεδ M)) :
    Function.Injective (fun f : M ⟶ (shift ε).obj M => f ≫ shiftLE hεσ M) := by
  subst σ
  exact h

/-- A sufficiently small increase of a fixed interleaving parameter can be
removed for finitely presented modules. -/
theorem finitelyPresented_exists_pos_interleaving_lowering
    (hM : FinitelyPresented (R := R) M) (hN : FinitelyPresented (R := R) N)
    (ε : ℝ≥0) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ δ : ℝ≥0, δ ≤ η →
      Nonempty (CoordinateInterleaving (ε + δ) M N) →
        Nonempty (CoordinateInterleaving ε M N) := by
  obtain ⟨η₁, hη₁, hMN⟩ :=
    finitelyPresented_exists_pos_postcomp_shiftLE_bijective M N hM hN ε
  obtain ⟨η₂, hη₂, hNM⟩ :=
    finitelyPresented_exists_pos_postcomp_shiftLE_bijective N M hN hM ε
  obtain ⟨η₃, hη₃, hMM⟩ :=
    finitelyPresented_exists_pos_postcomp_shiftLE_bijective M M hM hM (ε + ε)
  obtain ⟨η₄, hη₄, hNN⟩ :=
    finitelyPresented_exists_pos_postcomp_shiftLE_bijective N N hN hN (ε + ε)
  let η := min η₁ (min η₂ (min (η₃ / 2) (η₄ / 2)))
  have hη : 0 < η :=
    lt_min hη₁ (lt_min hη₂ (lt_min (half_pos hη₃) (half_pos hη₄)))
  refine ⟨η, hη, ?_⟩
  intro δ hδ ⟨i⟩
  have hδ₁ : δ ≤ η₁ := hδ.trans (min_le_left _ _)
  have hδ₂ : δ ≤ η₂ := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₃ : δ ≤ η₃ / 2 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ₄ : δ ≤ η₄ / 2 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htwice₃ : δ + δ ≤ η₃ := by
    calc
      δ + δ ≤ η₃ / 2 + η₃ / 2 := add_le_add hδ₃ hδ₃
      _ = η₃ := add_halves η₃
  have htwice₄ : δ + δ ≤ η₄ := by
    calc
      δ + δ ≤ η₄ / 2 + η₄ / 2 := add_le_add hδ₄ hδ₄
      _ = η₄ := add_halves η₄
  have hMM' : Function.Injective
      (fun f : M ⟶ (shift (ε + ε)).obj M =>
        f ≫ shiftLE (add_le_add (le_self_add : ε ≤ ε + δ) (le_self_add : ε ≤ ε + δ)) M) := by
    have heq : (ε + δ) + (ε + δ) = (ε + ε) + (δ + δ) := by ac_rfl
    exact injective_postcomp_shiftLE_congr M le_self_add _ heq.symm
      (hMM (δ + δ) htwice₃).1
  have hNN' : Function.Injective
      (fun f : N ⟶ (shift (ε + ε)).obj N =>
        f ≫ shiftLE (add_le_add (le_self_add : ε ≤ ε + δ) (le_self_add : ε ≤ ε + δ)) N) := by
    have heq : (ε + δ) + (ε + δ) = (ε + ε) + (δ + δ) := by ac_rfl
    exact injective_postcomp_shiftLE_congr N le_self_add _ heq.symm
      (hNN (δ + δ) htwice₄).1
  exact ⟨CoordinateInterleaving.of_postcomp_lifting le_self_add i
    (hMN δ hδ₁).2 (hNM δ hδ₂).2 hMM' hNN'⟩

/-- Every finite bound on the interleaving distance is attained by an actual
interleaving at that parameter. -/
theorem finitelyPresented_distance_le_iff_interleaving
    (hM : FinitelyPresented (R := R) M) (hN : FinitelyPresented (R := R) N)
    (ε : ℝ≥0) :
    coordinateInterleavingDistance M N ≤ (ε : ℝ≥0∞) ↔
      Nonempty (CoordinateInterleaving ε M N) := by
  constructor
  · intro h
    obtain ⟨η, hη, hlower⟩ :=
      finitelyPresented_exists_pos_interleaving_lowering hM hN ε
    have hlt : coordinateInterleavingDistance M N < ((ε + η : ℝ≥0) : ℝ≥0∞) :=
      h.trans_lt (ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right ε hη))
    obtain ⟨δ, hδ, ⟨i⟩⟩ := coordinateInterleavingDistance_lt_iff.mp hlt
    exact hlower η le_rfl ⟨i.mono (ENNReal.coe_lt_coe.mp hδ).le⟩
  · exact coordinateInterleavingDistance_le_of_nonempty

/-- A finite interleaving distance of finitely presented modules is attained. -/
theorem finitelyPresented_interleaving_at_distance
    (hM : FinitelyPresented (R := R) M) (hN : FinitelyPresented (R := R) N)
    (hf : coordinateInterleavingDistance M N ≠ ⊤) :
    Nonempty (CoordinateInterleaving (coordinateInterleavingDistance M N).toNNReal M N) := by
  apply (finitelyPresented_distance_le_iff_interleaving hM hN _).mp
  exact (ENNReal.coe_toNNReal hf).symm.le

/-- On finitely presented multiparameter modules, distance zero is precisely
natural isomorphism. -/
theorem finitelyPresented_distance_eq_zero_iff_iso
    (hM : FinitelyPresented (R := R) M) (hN : FinitelyPresented (R := R) N) :
    coordinateInterleavingDistance M N = 0 ↔ Nonempty (M ≅ N) := by
  constructor
  · intro h
    obtain ⟨i⟩ := (finitelyPresented_distance_le_iff_interleaving hM hN 0).mp
      (by simp [h])
    exact ⟨i.toIso⟩
  · rintro ⟨e⟩
    exact coordinateInterleavingDistance_eq_zero_of_iso e

/-- For finite distance, the admissible parameters form the closed upper ray
starting at the distance. -/
theorem finitelyPresented_interleaving_parameters_eq_Ici
    (hM : FinitelyPresented (R := R) M) (hN : FinitelyPresented (R := R) N)
    (hf : coordinateInterleavingDistance M N ≠ ⊤) :
    {ε : ℝ≥0 | Nonempty (CoordinateInterleaving ε M N)} =
      Set.Ici (coordinateInterleavingDistance M N).toNNReal := by
  ext ε
  rw [Set.mem_ofPred_eq, ← finitelyPresented_distance_le_iff_interleaving hM hN,
    ← ENNReal.coe_toNNReal hf, ENNReal.coe_le_coe]
  rfl

/-- The finite interleaving parameter set is closed, including when it is empty. -/
theorem finitelyPresented_isClosed_interleaving_parameters
    (hM : FinitelyPresented (R := R) M) (hN : FinitelyPresented (R := R) N) :
    IsClosed {ε : ℝ≥0 | Nonempty (CoordinateInterleaving ε M N)} := by
  by_cases hf : coordinateInterleavingDistance M N = ⊤
  · have he : {ε : ℝ≥0 | Nonempty (CoordinateInterleaving ε M N)} = ∅ := by
      ext ε
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hle := coordinateInterleavingDistance_le_of_nonempty h
      rw [hf] at hle
      exact ENNReal.coe_ne_top (top_le_iff.mp hle)
    rw [he]
    exact isClosed_empty
  · rw [finitelyPresented_interleaving_parameters_eq_Ici hM hN hf]
    exact isClosed_Ici

end TDA.Persistence.GradedFree
