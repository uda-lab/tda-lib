import TDA.Persistence.ConstructibleDefects
import TDA.Persistence.FiniteKernel
import TDA.Persistence.FiniteCokernel
import TDA.Persistence.RealInterleavingShortness

/-!
# Real shortness on finite critical samples

Critical samples evaluate the module at the grid values, as in `moduleDiagram`;
they differ from the padded zero-stage `sample` used in reconstruction.
Translate a critical parameter forward, then select the last critical value in
its cell. The intervening actual structure map is an isomorphism. Cancelling
that map transfers real transition annihilation to finite sampled defects.
The last observation remains fixed; no terminal zero stage is appended.
Cancellation works over rings. The finite shortness wrappers use the existing
field and same-carrier universe convention, without dimension assumptions.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory CategoryTheory.Limits RealShift
open scoped NNReal

variable {n : ℕ}

/-- Round a translated critical value down to the start of its actual grid cell.
This acts on critical samples, without the padded zero stage of `sample`. -/
noncomputable def sampleTranslation (c : Fin n ↪o ℝ) (δ : ℝ≥0) : Fin n →o Fin n where
  toFun i := ⟨(cellIndex c (c i + (δ : ℝ))).val - 1, by
    have hp := (lt_cellIndex_iff c i (c i + (δ : ℝ))).mpr
      (le_add_of_nonneg_right δ.coe_nonneg)
    have hq := (cellIndex c (c i + (δ : ℝ))).isLt
    omega⟩
  monotone' i j hij := Nat.sub_le_sub_right
    ((cellIndex c).monotone (add_le_add (c.monotone hij) (le_refl (δ : ℝ)))) 1

/-- The translated parameter is in the positive cell starting at the selected value. -/
theorem sampleTranslation_succ (c : Fin n ↪o ℝ) (δ : ℝ≥0) (i : Fin n) :
    (sampleTranslation c δ i).succ = cellIndex c (c i + (δ : ℝ)) := by
  apply Fin.ext
  have hp := (lt_cellIndex_iff c i (c i + (δ : ℝ))).mpr
    (le_add_of_nonneg_right δ.coe_nonneg)
  change (cellIndex c (c i + (δ : ℝ))).val - 1 + 1 = _
  omega

/-- Nonnegative real translation gives an inflationary critical-index map. -/
theorem le_sampleTranslation (c : Fin n ↪o ℝ) (δ : ℝ≥0) (i : Fin n) :
    i ≤ sampleTranslation c δ i := by
  have hp := (lt_cellIndex_iff c i (c i + (δ : ℝ))).mpr
    (le_add_of_nonneg_right δ.coe_nonneg)
  change i.val ≤ (cellIndex c (c i + (δ : ℝ))).val - 1
  omega

/-- Rounding never selects a critical value after the translated parameter. -/
theorem sampleTranslation_value_le (c : Fin n ↪o ℝ) (δ : ℝ≥0) (i : Fin n) :
    c (sampleTranslation c δ i) ≤ c i + (δ : ℝ) := by
  apply (lt_cellIndex_iff c _ _).mp
  rw [← sampleTranslation_succ c δ i]
  exact Nat.lt_succ_self _

/-- The selected critical value and translated parameter lie in the same cell. -/
theorem cellIndex_sampleTranslation (c : Fin n ↪o ℝ) (δ : ℝ≥0) (i : Fin n) :
    cellIndex c (c (sampleTranslation c δ i)) = cellIndex c (c i + (δ : ℝ)) := by
  rw [cellIndex_critical, sampleTranslation_succ]

/-- Zero translation is the identity on critical indices. -/
@[simp] theorem sampleTranslation_zero (c : Fin n ↪o ℝ) :
    sampleTranslation c 0 = OrderHom.id := by
  apply DFunLike.ext
  intro i
  apply Fin.succ_injective n
  rw [sampleTranslation_succ]
  simp

/-- The final observed index is fixed, even when its real cell is unbounded. -/
@[simp] theorem sampleTranslation_last (c : Fin (n + 1) ↪o ℝ) (δ : ℝ≥0) :
    sampleTranslation c δ (Fin.last n) = Fin.last n :=
  le_antisymm (Fin.le_last _) (le_sampleTranslation c δ _)

variable {R : Type u} [Ring R] {c : Fin n ↪o ℝ}
variable {A : PModule.{u,0,w} R ℝ}

/-- Actual real annihilation transfers to critical samples by cancelling the
within-cell isomorphism after the rounded endpoint. -/
theorem critical_structureMap_eq_zero (hA : IsConstructible c A) (δ : ℝ≥0)
    (hz : transition δ A = 0) (i : Fin n) :
    structureMap (reindex c.toOrderHom A) (le_sampleTranslation c δ i) = 0 := by
  have hv := sampleTranslation_value_le c δ i
  have : IsIso (structureMap A hv) := hA.isIso_map _ _ hv (cellIndex_sampleTranslation c δ i)
  apply (cancel_mono (structureMap A hv)).mp
  change structureMap A (c.monotone (le_sampleTranslation c δ i)) ≫ structureMap A hv =
    (0 : A.obj (c i) ⟶ A.obj (c (sampleTranslation c δ i))) ≫ structureMap A hv
  rw [zero_comp, structureMap_comp]
  exact congrArg (fun f => f.app (c i)) hz

variable {k : Type u} [Field k] {M N : PModule.{u,0,u} k ℝ}

/-- The critical sample of a constructible, real-short module is finite-translation-trivial. -/
theorem critical_translationTrivial (hM : IsConstructible c M) (δ : ℝ≥0)
    (hz : transition δ M = 0) :
    TranslationTrivial (sampleTranslation c δ) (le_sampleTranslation c δ)
      (reindex c.toOrderHom M) := critical_structureMap_eq_zero hM δ hz

/-- A natural isomorphism transports finite shortness through its actual naturality square. -/
theorem translationTrivial_of_iso {B C : PModule.{u,0,u} k (Fin n)}
    (θ : Fin n →o Fin n) (hθ : ∀ i, i ≤ θ i) (e : B ≅ C)
    (hB : TranslationTrivial θ hθ B) : TranslationTrivial θ hθ C := by
  intro i
  apply (cancel_epi (e.hom.app i)).mp
  rw [comp_zero]
  change e.hom.app i ≫ C.map (homOfLE (hθ i)) = 0
  rw [← e.hom.naturality]
  change structureMap B (hθ i) ≫ e.hom.app (θ i) = 0
  rw [hB i, zero_comp]

/-- Sampling the actual morphism gives an actual finite kernel with derived shortness. -/
theorem criticalKernel_translationTrivial (hM : IsConstructible c M)
    (hN : IsConstructible c N) (f : M ⟶ N) (δ : ℝ≥0)
    (hz : transition δ (kernel f) = 0) :
    TranslationTrivial (sampleTranslation c δ) (le_sampleTranslation c δ)
      (finiteKernel (reindexNatTrans c.toOrderHom f)) :=
  translationTrivial_of_iso _ _ (criticalKernelIso c f)
    (critical_translationTrivial (hM.kernel hN f) δ hz)

/-- The actual finite sampled cokernel inherits real shortness through its natural comparison. -/
theorem criticalCokernel_translationTrivial (hM : IsConstructible c M)
    (hN : IsConstructible c N) (f : M ⟶ N) (δ : ℝ≥0)
    (hz : transition δ (cokernel f) = 0) :
    TranslationTrivial (sampleTranslation c δ) (le_sampleTranslation c δ)
      (finiteCokernel (reindexNatTrans c.toOrderHom f)) :=
  translationTrivial_of_iso _ _ (criticalCokernelIso c f)
    (critical_translationTrivial (hM.cokernel hN f) δ hz)

/-- An actual interleaving supplies constructible real defects and both finite
sampled shortness statements on the constructed common grid. No shortness is an input. -/
theorem interleaving_critical_defects {m : ℕ} {d : Fin m ↪o ℝ} {ε : ℝ≥0}
    (hM : IsConstructible c M) (hN : IsConstructible d N) (i : RealInterleaving ε M N) :
    let e := commonGrid c (shiftGrid ε d)
    IsConstructible e (kernel i.φ) ∧ IsConstructible e (cokernel i.φ) ∧
      TranslationTrivial (sampleTranslation e (ε + ε)) (le_sampleTranslation e (ε + ε))
        (finiteKernel (reindexNatTrans e.toOrderHom i.φ)) ∧
      TranslationTrivial (sampleTranslation e (ε + ε)) (le_sampleTranslation e (ε + ε))
        (finiteCokernel (reindexNatTrans e.toOrderHom i.φ)) := by
  obtain ⟨hMe, hNe⟩ := common_shift_constructible hM hN ε
  exact ⟨hMe.kernel hNe i.φ, hMe.cokernel hNe i.φ,
    criticalKernel_translationTrivial hMe hNe i.φ (ε + ε) i.kernel_transition_eq_zero,
    criticalCokernel_translationTrivial hMe hNe i.φ (ε + ε) i.cokernel_transition_eq_zero⟩

end TDA.Persistence.FiniteConstructible
