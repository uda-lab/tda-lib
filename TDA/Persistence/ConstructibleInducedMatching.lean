import TDA.Persistence.RealInducedMatching

/-!
# Actual constructible morphisms give real induced occurrence matchings

The hypotheses on the two defects are vanishing of their actual real
transitions. Constructibility transfers them to actual sampled kernel/cokernel
shortness. The finite induced partial injection is then transported to the
canonical real finite and essential occurrence labels, with exact real bounds.
An actual interleaving derives both defect hypotheses on its constructed
common grid with the shifted target.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory CategoryTheory.Limits RealShift
open scoped Classical NNReal

variable {n m : ℕ} {k : Type u} [Field k]
variable (c : Fin n ↪o ℝ) (M N : PModule.{u,0,u} k ℝ)
variable (hfdM : ∀ j, FiniteDimensional k (M.obj (c j)))
variable (hfdN : ∀ j, FiniteDimensional k (N.obj (c j)))
variable (hM : IsConstructible c M) (hN : IsConstructible c N) (f : M ⟶ N)
variable (δK δC : ℝ≥0)
variable (hk : transition δK (kernel f) = 0) (hc : transition δC (cokernel f) = 0)

/-- Construct the real occurrence matching from the actual sampled induced map.
Only actual real defect annihilation and critical-fiber finiteness are supplied. -/
noncomputable def inducedOccurrenceMatching :
    OccurrenceMatching (moduleDiagram c M hfdM).finiteOccurrences
      (moduleDiagram c N hfdN).finiteOccurrences
      (moduleDiagram c M hfdM).essentialOccurrences (moduleDiagram c N hfdN).essentialOccurrences := by
  letI : ∀ i, FiniteDimensional k ((reindex c.toOrderHom M).obj i) := hfdM
  letI : ∀ i, FiniteDimensional k ((reindex c.toOrderHom N).obj i) := hfdN
  exact FiniteBarcode.RealInduced.matching c (reindexNatTrans c.toOrderHom f) δK δC
    (criticalKernel_translationTrivial hM hN f δK hk)
    (criticalCokernel_translationTrivial hM hN f δC hc)

/-- Exact real endpoint bounds, essential bijection and unmatched-length bounds
are derived for the actual morphism; no grid-rounding term is added. -/
theorem inducedOccurrenceMatching_bounds : RealMatchingBounds δK δC
    (inducedOccurrenceMatching c M N hfdM hfdN hM hN f δK δC hk hc) := by
  let : ∀ i, FiniteDimensional k ((reindex c.toOrderHom M).obj i) := hfdM
  let : ∀ i, FiniteDimensional k ((reindex c.toOrderHom N).obj i) := hfdN
  exact FiniteBarcode.RealInduced.matching_bounds c (reindexNatTrans c.toOrderHom f) δK δC
    (criticalKernel_translationTrivial hM hN f δK hk)
    (criticalCokernel_translationTrivial hM hN f δC hc)

omit hfdM hfdN hM hN f δK δC hk hc

/-- An actual interleaving supplies a real induced matching into its actual
shifted target diagram, with derived double-shift bounds and essential coverage.
No common grid, new-fiber finiteness, shortness or matching witness is assumed. -/
theorem interleaving_shifted_induced_matching {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}
    {M N : PModule.{u,0,u} k ℝ} (hM : IsConstructible c M) (hN : IsConstructible d N)
    (hfdM : ∀ j, FiniteDimensional k (M.obj (c j)))
    (hfdN : ∀ j, FiniteDimensional k (N.obj (d j)))
    {ε : ℝ≥0} (i : RealInterleaving ε M N) :
    ∃ A : OccurrenceMatching (moduleDiagram c M hfdM).finiteOccurrences
        (translateDiagram (moduleDiagram d N hfdN) (-(ε : ℝ))).finiteOccurrences
        (moduleDiagram c M hfdM).essentialOccurrences
        (translateDiagram (moduleDiagram d N hfdN) (-(ε : ℝ))).essentialOccurrences,
      RealMatchingBounds (ε + ε) (ε + ε) A := by
  let e := commonGrid c (shiftGrid ε d)
  obtain ⟨hMe, hNe⟩ := common_shift_constructible hM hN ε
  let hMeFD := fun j => finiteDimensional_of_isConstructible M hM hfdM (e j)
  let hNeFD := fun j => finiteDimensional_of_isConstructible ((shift ε).obj N) (hN.shift ε)
    (finiteDimensional_shiftedCritical d N hfdN ε) (e j)
  let A := inducedOccurrenceMatching e M ((shift ε).obj N) hMeFD hNeFD hMe hNe i.φ
    (ε + ε) (ε + ε) i.kernel_transition_eq_zero i.cokernel_transition_eq_zero
  have H : ∃ B : OccurrenceMatching (moduleDiagram e M hMeFD).finiteOccurrences
      (moduleDiagram e ((shift ε).obj N) hNeFD).finiteOccurrences
      (moduleDiagram e M hMeFD).essentialOccurrences
      (moduleDiagram e ((shift ε).obj N) hNeFD).essentialOccurrences,
      RealMatchingBounds (ε + ε) (ε + ε) B :=
    ⟨A, inducedOccurrenceMatching_bounds e M ((shift ε).obj N) hMeFD hNeFD hMe hNe i.φ
      (ε + ε) (ε + ε) i.kernel_transition_eq_zero i.cokernel_transition_eq_zero⟩
  rw [moduleDiagram_refinement M (refines_commonGrid_left c (shiftGrid ε d)) hM hfdM,
    moduleDiagram_shift_refinement d e N hN hfdN ε (refines_commonGrid_right c (shiftGrid ε d))] at H
  exact H

end TDA.Persistence.FiniteConstructible
