import TDA.Persistence.SupportInterval
import TDA.Persistence.AlgebraicFamily
import TDA.Persistence.CutSubspacesExamples

/-!
The real-indexed algebraic sum of all singleton interval modules is the
ephemeral persistence module: one rational line at every real parameter and
zero maps across strict inequalities. The occurrence type is all of `ℝ`.
-/

set_option autoImplicit false

namespace TDA.Persistence.IntervalCompatibility

open CategoryTheory

/-- The supported module on one real parameter. -/
@[reducible]
noncomputable def singletonModule (j : ℝ) : PModule.{0,0,0} ℚ ℝ :=
  SupportInterval.module (k := ℚ) ({j} : Set ℝ) Set.ordConnected_singleton

/-- The algebraic sum has one occurrence for each real parameter. -/
@[reducible]
noncomputable def singletonFamily : PModule.{0,0,0} ℚ ℝ :=
  AlgebraicFamily.familyModule singletonModule

/-- Evaluate an algebraic-sum vector at the unique summand active at `t`. -/
@[reducible]
noncomputable def evaluation (t : ℝ) : singletonFamily.obj t →ₗ[ℚ] ℚ :=
  (Submodule.subtype (SupportInterval.fiber (k := ℚ) ({t} : Set ℝ) t)).comp
    (DirectSum.component ℚ ℝ (fun j => (singletonModule j).obj t) t)

theorem evaluation_surjective (t : ℝ) : Function.Surjective (evaluation t) := by
  classical
  intro q
  let v : SupportInterval.fiber (k := ℚ) ({t} : Set ℝ) t :=
    ⟨q, by simp [SupportInterval.fiber]⟩
  refine ⟨DirectSum.lof ℚ ℝ (fun j => (singletonModule j).obj t) t v, ?_⟩
  change ((DirectSum.component ℚ ℝ (fun j => (singletonModule j).obj t) t
    (DirectSum.lof ℚ ℝ (fun j => (singletonModule j).obj t) t v) :
      SupportInterval.fiber (k := ℚ) ({t} : Set ℝ) t) : ℚ) = q
  simp [v]

theorem evaluation_injective (t : ℝ) : Function.Injective (evaluation t) := by
  classical
  intro x y h
  change DirectSum ℝ (fun j => (singletonModule j).obj t) at x y
  apply DFinsupp.ext
  intro j
  by_cases hj : j = t
  · subst j
    apply Subtype.ext
    exact h
  · have htj : t ∉ ({j} : Set ℝ) := by simpa using (Ne.symm hj)
    apply Subtype.ext
    exact (SupportInterval.val_eq_zero (k := ℚ) ({j} : Set ℝ) htj (x j)).trans
      (SupportInterval.val_eq_zero (k := ℚ) ({j} : Set ℝ) htj (y j)).symm

private theorem evaluation_strict_map_zero {s t : ℝ} (h : s < t)
    (x : singletonFamily.obj s) :
    evaluation t (structureMapLinear singletonFamily h.le x) = 0 := by
  classical
  have hz : structureMapLinear (singletonModule t) h.le = 0 :=
    (SupportInterval.structureMap_eq_zero_iff (k := ℚ) ({t} : Set ℝ)
      Set.ordConnected_singleton h.le).mpr (by
        intro hh
        exact (ne_of_lt h) (by simpa using hh.1))
  have hcomp : DirectSum.component ℚ ℝ (fun j => (singletonModule j).obj t) t
      (structureMapLinear singletonFamily h.le x) = 0 := by
    rw [AlgebraicFamily.structureMap_apply singletonModule h.le x t, hz]
    rfl
  change (Submodule.subtype (SupportInterval.fiber (k := ℚ) ({t} : Set ℝ) t))
    (DirectSum.component ℚ ℝ (fun j => (singletonModule j).obj t) t
      (structureMapLinear singletonFamily h.le x)) = 0
  rw [hcomp]
  rfl

/-- The unique active coordinate gives a linear isomorphism at each fiber. -/
noncomputable def evaluationIso (t : ℝ) :
    singletonFamily.obj t ≅ CutSubspacesExamples.ephemeralModule.obj t :=
  (LinearEquiv.ofBijective (evaluation t)
    ⟨evaluation_injective t, evaluation_surjective t⟩).toModuleIso

/-- Explicit natural isomorphism from the algebraic direct sum over *all*
real singleton intervals to the rational ephemeral module. -/
noncomputable def ephemeralIso :
    singletonFamily ≅ CutSubspacesExamples.ephemeralModule := by
  refine NatIso.ofComponents evaluationIso ?_
  intro s t f
  by_cases hst : s = t
  · subst t
    have hf : f = 𝟙 s := Subsingleton.elim _ _
    subst f
    rw [singletonFamily.map_id, CutSubspacesExamples.ephemeralModule.map_id]
    rw [Category.id_comp, Category.comp_id]
  · have hlt : s < t := lt_of_le_of_ne (leOfHom f) hst
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change evaluation t (structureMapLinear singletonFamily hlt.le x) =
      structureMapLinear CutSubspacesExamples.ephemeralModule hlt.le (evaluation s x)
    rw [evaluation_strict_map_zero hlt x,
      CutSubspacesExamples.ephemeralModule_strict_map_zero hlt]
    rfl

end TDA.Persistence.IntervalCompatibility
