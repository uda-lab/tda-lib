import TDA.Persistence.ConstructibleRefinementBarcode
import TDA.Persistence.DiagramBottleneckTranslation

/-!
# Actual real shift diagrams and occurrence untranslation

Positive evaluation at `t+ε` translates critical values and both finite endpoints
by `−ε`. The critical restrictions are naturally isomorphic through equality of
their real indices. Rank-barcode invariance then proves the diagram formula,
also on refinements with their finiteness derived from constructibility.

Translation supplies actual finite and essential occurrence equivalences. Their
inverses add ε back to endpoint values and relabel the target of a matching.
The constructed complete matching below compares a module with its own shift;
the induced matching for two arbitrary interleaved modules is a separate result.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory RealShift
open scoped Classical ENNReal NNReal

namespace FiniteConstructible

variable {n m : ℕ}

/-- The actual shifted critical restriction compares through `(c_i−ε)+ε=c_i`. -/
def shiftedCriticalIso {R : Type u} [Ring R] (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,w} R ℝ) (ε : ℝ≥0) :
    reindex (shiftGrid ε c).toOrderHom ((shift ε).obj M) ≅ reindex c.toOrderHom M := by
  let e : ((translation ε).comp (shiftGrid ε c).toOrderHom).toFunctor ≅
      c.toOrderHom.toFunctor :=
    NatIso.ofComponents (fun i => eqToIso (sub_add_cancel (c i) (ε : ℝ)))
      (by intros; apply Subsingleton.elim)
  exact Functor.isoWhiskerRight e M

variable {k : Type u} [Field k]

/-- Finiteness at shifted critical fibers follows from the equality of actual indices. -/
theorem finiteDimensional_shiftedCritical (c : Fin n ↪o ℝ)
    (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) (ε : ℝ≥0) (i : Fin n) :
    FiniteDimensional k (((shift ε).obj M).obj (shiftGrid ε c i)) := by
  change FiniteDimensional k (M.obj (c i - (ε : ℝ) + (ε : ℝ)))
  rw [sub_add_cancel]
  exact hfd i

private theorem endpoints_shift (c : Fin n ↪o ℝ) (ε : ℝ≥0) (I : FiniteInterval n) :
    RealBarcode.endpoints (shiftGrid ε c) I =
      translateDiagramPoint (-(ε : ℝ)) (RealBarcode.endpoints c I) := by
  dsimp only [RealBarcode.endpoints, translateDiagramPoint]
  split_ifs <;> simp [shiftGrid_apply, sub_eq_add_neg]

/-- Relabel actual index bars by the shifted real grid, with terminal deaths still top. -/
theorem ofIndexBars_shiftGrid (c : Fin n ↪o ℝ) (ε : ℝ≥0)
    (B : Multiset (FiniteInterval n)) :
    ofIndexBars (shiftGrid ε c) (shiftGrid ε c).strictMono B =
      translateDiagram (ofIndexBars c c.strictMono B) (-(ε : ℝ)) := by
  apply Diagram.ext
  change B.map (RealBarcode.endpoints (shiftGrid ε c)) =
    (B.map (RealBarcode.endpoints c)).map (translateDiagramPoint (-(ε : ℝ)))
  rw [Multiset.map_map]
  congr 1
  funext I
  exact endpoints_shift c ε I

/-- Actual critical-module isomorphism and rank-barcode invariance give the shift formula.
Constructibility is unnecessary on the native shifted grid. -/
theorem moduleDiagram_shift (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) (ε : ℝ≥0) :
    moduleDiagram (shiftGrid ε c) ((shift ε).obj M)
        (finiteDimensional_shiftedCritical c M hfd ε) =
      translateDiagram (moduleDiagram c M hfd) (-(ε : ℝ)) := by
  let : ∀ i, FiniteDimensional k ((reindex c.toOrderHom M).obj i) := hfd
  let : ∀ i, FiniteDimensional k
      ((reindex (shiftGrid ε c).toOrderHom ((shift ε).obj M)).obj i) :=
    finiteDimensional_shiftedCritical c M hfd ε
  unfold moduleDiagram
  rw [rankBarcode_eq_of_iso (shiftedCriticalIso c M ε), ofIndexBars_shiftGrid]

/-- On a refinement of the shifted grid, derive all new finiteness before computing
the same real shifted diagram. -/
theorem moduleDiagram_shift_refinement (c : Fin n ↪o ℝ) (e : Fin m ↪o ℝ)
    (M : PModule.{u,0,u} k ℝ) (hM : IsConstructible c M)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) (ε : ℝ≥0)
    (he : Refines (shiftGrid ε c) e) :
    moduleDiagram e ((shift ε).obj M)
        (fun j => finiteDimensional_of_isConstructible ((shift ε).obj M) (hM.shift ε)
          (finiteDimensional_shiftedCritical c M hfd ε) (e j)) =
      translateDiagram (moduleDiagram c M hfd) (-(ε : ℝ)) := by
  rw [moduleDiagram_refinement ((shift ε).obj M) he (hM.shift ε)
    (finiteDimensional_shiftedCritical c M hfd ε), moduleDiagram_shift]

/-- The source's inverse barcode shift adds ε back to both finite endpoints. -/
theorem moduleDiagram_unshift (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) (ε : ℝ≥0) :
    translateDiagram (moduleDiagram (shiftGrid ε c) ((shift ε).obj M)
      (finiteDimensional_shiftedCritical c M hfd ε)) (ε : ℝ) =
        moduleDiagram c M hfd := by
  rw [moduleDiagram_shift, translateDiagram_add, neg_add_cancel, translateDiagram_zero]

/-- A module and its actual shift have a constructed complete occurrence matching.
Every endpoint evaluation and the cost bound are proved, with no matching input. -/
theorem exists_shift_matching (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) (ε : ℝ≥0) :
    let D := moduleDiagram c M hfd
    let E := moduleDiagram (shiftGrid ε c) ((shift ε).obj M)
      (finiteDimensional_shiftedCritical c M hfd ε)
    ∃ A : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
        D.essentialOccurrences E.essentialOccurrences,
      (∀ i, ∃ j, A.finite i = some j ∧
        j.1 = (i.1.1 - (ε : ℝ), i.1.2 - (ε : ℝ))) ∧
      (∀ j, ∃ i, A.finite i = some j) ∧
      (∀ i, (A.essential i).1 = i.1 - (ε : ℝ)) ∧
      A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ ε := by
  dsimp only
  rw [moduleDiagram_shift]
  let D := moduleDiagram c M hfd
  refine ⟨translatedMatching D (-(ε : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨finiteTranslationEquiv D (-(ε : ℝ)) i, rfl, ?_⟩
    simpa only [sub_eq_add_neg] using finiteTranslationEquiv_value D (-(ε : ℝ)) i
  · intro j
    refine ⟨(finiteTranslationEquiv D (-(ε : ℝ))).symm j, ?_⟩
    simp only [translatedMatching, Equiv.apply_symm_apply]
  · intro i
    simpa only [translatedMatching, sub_eq_add_neg] using
      essentialTranslationEquiv_value D (-(ε : ℝ)) i
  · simpa only [abs_neg, abs_of_nonneg ε.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
      translatedMatching_cost_le D (-(ε : ℝ))

/-- The complete matching also uses the actual diagram on any shifted-grid
refinement; added critical-fiber finiteness is derived rather than assumed. -/
theorem exists_shift_refinement_matching (c : Fin n ↪o ℝ) (e : Fin m ↪o ℝ)
    (M : PModule.{u,0,u} k ℝ) (hM : IsConstructible c M)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) (ε : ℝ≥0)
    (he : Refines (shiftGrid ε c) e) :
    let D := moduleDiagram c M hfd
    let E := moduleDiagram e ((shift ε).obj M)
      (fun j => finiteDimensional_of_isConstructible ((shift ε).obj M) (hM.shift ε)
        (finiteDimensional_shiftedCritical c M hfd ε) (e j))
    ∃ A : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
        D.essentialOccurrences E.essentialOccurrences,
      (∀ i, ∃ j, A.finite i = some j ∧
        j.1 = (i.1.1 - (ε : ℝ), i.1.2 - (ε : ℝ))) ∧
      (∀ j, ∃ i, A.finite i = some j) ∧
      (∀ i, (A.essential i).1 = i.1 - (ε : ℝ)) ∧
      A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ ε := by
  dsimp only
  rw [moduleDiagram_shift_refinement c e M hM hfd ε he]
  have h := exists_shift_matching c M hfd ε
  dsimp only at h
  rw [moduleDiagram_shift] at h
  exact h

end FiniteConstructible
end TDA.Persistence
