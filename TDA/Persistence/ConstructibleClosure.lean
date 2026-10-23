import TDA.Persistence.ConstructibleIsometry
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Attainment and separation for finite-constructible real modules

For right-continuous finite-constructible modules with finite-dimensional critical
fibers, the finite barcode isometry and an optimal occurrence matching attain every
finite interleaving-distance bound. Consequently the admissible parameters form a
closed ray, and distance zero is equivalent to a natural isomorphism.

This is the one-dimensional finite-constructible case of Lesnick's closure theorem
(arXiv:1106.5305v4, Theorem 6.1 and Remark 6.3). It does not assert closure for general
real-indexed modules or establish the multidimensional finite-presentation theorem.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory
open scoped NNReal ENNReal

variable {k : Type u} [Field k] {n m : ℕ}
variable {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ} {M N : PModule.{u,0,u} k ℝ}
variable (hM : IsConstructible c M) (hN : IsConstructible d N)
variable (hfdM : ∀ i, FiniteDimensional k (M.obj (c i)))
variable (hfdN : ∀ j, FiniteDimensional k (N.obj (d j)))

include hM hN hfdM hfdN

/-- A finite distance bound is attained by an interleaving, including equality. -/
theorem distance_le_iff_interleaving (ε : ℝ≥0) :
    realInterleavingDistance M N ≤ (ε : ℝ≥0∞) ↔
      Nonempty (RealInterleaving ε M N) := by
  constructor
  · intro h
    have hb : bottleneck (moduleDiagram c M hfdM) (moduleDiagram d N hfdN) ≤ ε := by
      rw [bottleneck_eq_distance hM hN hfdM hfdN]
      exact h
    have hf := hb.trans_lt (ENNReal.coe_lt_top (r := ε))
    obtain ⟨A, hA⟩ := (bottleneck_optimal_iff _ _).mpr
      ((bottleneck_lt_top_iff _ _).mp hf)
    exact ⟨matchingInterleaving c d M N hM hN hfdM hfdN ε A (hA.le.trans hb)⟩
  · exact realInterleavingDistance_le_of_nonempty

/-- The extended distance admits a witness at its value whenever it is finite. -/
theorem interleaving_at_distance (hf : realInterleavingDistance M N ≠ ⊤) :
    Nonempty (RealInterleaving (realInterleavingDistance M N).toNNReal M N) := by
  apply (distance_le_iff_interleaving hM hN hfdM hfdN _).mp
  exact (ENNReal.coe_toNNReal hf).symm.le

/-- Distance zero separates finite-constructible modules up to natural isomorphism. -/
theorem distance_eq_zero_iff_iso :
    realInterleavingDistance M N = 0 ↔ Nonempty (M ≅ N) := by
  constructor
  · intro h
    obtain ⟨i⟩ := (distance_le_iff_interleaving hM hN hfdM hfdN 0).mp (by simp [h])
    exact ⟨i.toIso⟩
  · rintro ⟨e⟩
    exact realInterleavingDistance_eq_zero_of_iso e

/-- For finite distance, the interleaving parameters form its closed upper ray. -/
theorem interleaving_parameters_eq_Ici (hf : realInterleavingDistance M N ≠ ⊤) :
    {ε : ℝ≥0 | Nonempty (RealInterleaving ε M N)} =
      Set.Ici (realInterleavingDistance M N).toNNReal := by
  ext ε
  rw [Set.mem_ofPred_eq, ← distance_le_iff_interleaving hM hN hfdM hfdN,
    ← ENNReal.coe_toNNReal hf, ENNReal.coe_le_coe]
  rfl

/-- Admissible finite interleaving parameters are closed, also at infinite distance. -/
theorem isClosed_interleaving_parameters :
    IsClosed {ε : ℝ≥0 | Nonempty (RealInterleaving ε M N)} := by
  by_cases hf : realInterleavingDistance M N = ⊤
  · have he : {ε : ℝ≥0 | Nonempty (RealInterleaving ε M N)} = ∅ := by
      ext ε
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hle := realInterleavingDistance_le_of_nonempty h
      rw [hf] at hle
      exact ENNReal.coe_ne_top (top_le_iff.mp hle)
    rw [he]
    exact isClosed_empty
  · rw [interleaving_parameters_eq_Ici hM hN hfdM hfdN hf]
    exact isClosed_Ici

end TDA.Persistence.FiniteConstructible
