import TDA.Persistence.ConstructibleScaleBarcode
import TDA.Persistence.SublevelConstructible
import TDA.Persistence.CechRipsInterleaving
import TDA.Filtration.FilterFunctionMap

/-!
# Positive scaling of sublevel persistence modules

The sublevel module of a positively scaled filter is the positively scaled original sublevel
module. This gives the ring-level distance law, the scaled finite-constructible diagram formula,
and the corresponding logarithmic shift isomorphism. These are library extensions proved from the
merged filtration, module, and constructible-diagram definitions; no log-diagram translation is
asserted here.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits RealShift
open TDA.Filtration
open TDA.Persistence.FiniteConstructible
open scoped Classical ENNReal NNReal

variable {V : Type u} [LinearOrder V]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TDA.Simplicial.TotalFace K)]
variable (R : Type v) [Ring R] (n : ℕ)

/-! ### The sublevel bridge -/

omit [LinearOrder V] [Fintype (TDA.Simplicial.TotalFace K)] in
/-- The sublevel filtration of a scaled filter is the scaled reindexing of the original one. -/
theorem sublevelFiltration_scale (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) :
      (f.scale c hc).sublevelFiltration =
      Filtration.reindex (PModule.scaleHom c hc) f.sublevelFiltration := by
  apply OrderHom.ext
  funext r
  change (f.scale c hc).sublevel r = f.sublevel (PModule.scaleHom c hc r)
  rw [FilterFunction.scale_sublevel]
  rfl

omit [Fintype (TDA.Simplicial.TotalFace K)] in
/-- The homology persistence module of a scaled filter is the scaled original module. -/
theorem sublevelModule_scale (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) :
    sublevelModule R (f.scale c hc) n =
      PModule.scale c hc (sublevelModule R f n) := by
  change simplicialHomologyPModule R (f.scale c hc).sublevelFiltration n =
    PModule.scale c hc (simplicialHomologyPModule R f.sublevelFiltration n)
  rw [sublevelFiltration_scale f c hc]
  rfl

omit [Fintype (TDA.Simplicial.TotalFace K)] in
/-- Scaling multiplies the interleaving distance of sublevel modules over any ring. -/
theorem realInterleavingDistance_sublevelModule_scale
    (f g : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) :
    realInterleavingDistance (sublevelModule R (f.scale c hc) n)
        (sublevelModule R (g.scale c hc) n) =
      ENNReal.ofReal c * realInterleavingDistance (sublevelModule R f n)
        (sublevelModule R g n) := by
  rw [sublevelModule_scale, sublevelModule_scale]
  exact realInterleavingDistance_scale c hc _ _

/-- The scaled sublevel module is constructible on the scaled critical-value grid. -/
theorem sublevelModule_scale_isConstructible (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) :
    IsConstructible (FiniteConstructible.scaleGrid c hc f.criticalValue)
      (sublevelModule R (f.scale c hc) n) := by
  rw [sublevelModule_scale]
  exact IsConstructible.scale (sublevelModule_isConstructible R n f) c hc

variable {k : Type u} [Field k]

/-- Finite-dimensionality of the scaled sublevel module on the scaled critical grid. -/
theorem sublevelModule_scale_finiteDimensional (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) :
    ∀ i, FiniteDimensional k
      ((sublevelModule k (f.scale c hc) n).obj
        (FiniteConstructible.scaleGrid c hc f.criticalValue i)) := by
  intro i
  rw [sublevelModule_scale]
  exact finiteDimensional_scaledCritical (sublevelModule_finiteDimensional k n f) c hc i

private theorem moduleDiagram_eq_of_eq {m : ℕ} {g : Fin m ↪o ℝ}
    {M N : PModule.{u,0,u} k ℝ} (h : M = N)
    (hM : ∀ i, FiniteDimensional k (M.obj (g i)))
    (hN : ∀ i, FiniteDimensional k (N.obj (g i))) :
    moduleDiagram g M hM = moduleDiagram g N hN := by
  cases h
  rfl

/-- The module diagram on the scaled critical grid agrees with the actual scaled filter diagram. -/
theorem moduleDiagram_sublevelModule_scale (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) :
    moduleDiagram (FiniteConstructible.scaleGrid c hc f.criticalValue)
        (sublevelModule k (f.scale c hc) n)
        (sublevelModule_scale_finiteDimensional (k := k) (n := n) f c hc) =
      dgm k (f.scale c hc) n := by
  calc
    moduleDiagram (FiniteConstructible.scaleGrid c hc f.criticalValue)
        (sublevelModule k (f.scale c hc) n)
        (sublevelModule_scale_finiteDimensional (k := k) (n := n) f c hc) =
        moduleDiagram (FiniteConstructible.scaleGrid c hc f.criticalValue)
          (PModule.scale c hc (sublevelModule k f n))
          (finiteDimensional_scaledCritical (sublevelModule_finiteDimensional k n f) c hc) := by
      exact moduleDiagram_eq_of_eq (sublevelModule_scale k n f c hc)
        (sublevelModule_scale_finiteDimensional (k := k) (n := n) f c hc)
        (finiteDimensional_scaledCritical (sublevelModule_finiteDimensional k n f) c hc)
    _ = (moduleDiagram f.criticalValue (sublevelModule k f n)
          (sublevelModule_finiteDimensional k n f)).scale c hc := by
            exact moduleDiagram_scale f.criticalValue (sublevelModule k f n)
              (sublevelModule_finiteDimensional k n f) c hc
    _ = (dgm k f n).scale c hc := by
      rw [moduleDiagram_sublevelModule]
    _ = dgm k (f.scale c hc) n := (dgm_scale k f n hc).symm

/-! ### Logarithmic scaling -/

private theorem logModule_scale_index {c : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (t : ℝ) :
    (PModule.scaleHom c hc).comp
        (expHom.comp (translation (logParam c))) t = expHom t := by
  change c⁻¹ * Real.exp (t + (logParam c : ℝ)) = Real.exp t
  rw [exp_add_logParam hc1 t]
  exact inv_mul_cancel_left₀ hc.ne' _

omit [Fintype (TDA.Simplicial.TotalFace K)] in
private theorem logModule_scale_source_eq (f : FilterFunction K ℝ) {c : ℝ}
    (hc : 0 < c) (t : ℝ) :
    ((shift (logParam c)).obj (logModule R (f.scale c hc) n)).obj t =
      (sublevelModule R f n).obj
        ((PModule.scaleHom c hc).comp
          (expHom.comp (translation (logParam c))) t) := by
  rw [shift_obj, logModule_eq_reindex R n (f.scale c hc), sublevelModule_scale]
  rfl

omit [Fintype (TDA.Simplicial.TotalFace K)] in
private theorem logModule_scale_target_eq (f : FilterFunction K ℝ) (t : ℝ) :
    (sublevelModule R f n).obj (expHom t) = (logModule R f n).obj t := by
  rw [logModule_eq_reindex R n f]
  rfl

omit [Fintype (TDA.Simplicial.TotalFace K)] in
private theorem logModule_scale_source_functor_eq (f : FilterFunction K ℝ) {c : ℝ}
    (hc : 0 < c) :
    (shift (logParam c)).obj (logModule R (f.scale c hc) n) =
      reindex ((PModule.scaleHom c hc).comp
        (expHom.comp (translation (logParam c)))) (sublevelModule R f n) := by
  rw [logModule_eq_reindex R n (f.scale c hc), sublevelModule_scale]
  rfl

omit [Fintype (TDA.Simplicial.TotalFace K)] in
private theorem logModule_scale_target_functor_eq (f : FilterFunction K ℝ) :
    reindex expHom (sublevelModule R f n) = logModule R f n :=
  (logModule_eq_reindex R n f).symm

/-- Components of a natural transformation conjugated by functor equalities. -/
private theorem eqToHom_comp_comp_eqToHom_app {C : Type*} [Category C] {D : Type*} [Category D]
    {F F' G' G : C ⥤ D} (p : F = F') (α : F' ⟶ G') (q : G' = G) (t : C) :
    (eqToHom p ≫ α ≫ eqToHom q).app t =
      eqToHom (by rw [p]) ≫ α.app t ≫ eqToHom (by rw [q]) := by
  subst p q
  simp

/-- Positive filter scaling becomes a logarithmic shift, with the componentwise transport shown. -/
noncomputable def logModule_scale_shiftIso (f : FilterFunction K ℝ) {c : ℝ} (hc : 0 < c)
    (hc1 : 1 ≤ c) :
    (shift (logParam c)).obj (logModule R (f.scale c hc) n) ≅ logModule R f n := by
  exact eqToIso (logModule_scale_source_functor_eq R n f hc) ≪≫
    Functor.isoWhiskerRight
      (NatIso.ofComponents (fun t => eqToIso (logModule_scale_index hc hc1 t))
        (by intros; apply Subsingleton.elim)) (sublevelModule R f n) ≪≫
      eqToIso (logModule_scale_target_functor_eq R n f)

/-- The logarithmic scaling isomorphism is transport of the sublevel module along
`c⁻¹ * exp (t + log c) = exp t`. -/
theorem logModule_scale_shiftIso_hom_app (f : FilterFunction K ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (t : ℝ) :
    (logModule_scale_shiftIso R n f hc hc1).hom.app t =
    eqToHom (logModule_scale_source_eq R n f hc t) ≫
        (sublevelModule R f n).map (eqToHom (logModule_scale_index hc hc1 t)) ≫
        eqToHom (logModule_scale_target_eq R n f t) := by
  exact eqToHom_comp_comp_eqToHom_app (logModule_scale_source_functor_eq R n f hc) _
    (logModule_scale_target_functor_eq R n f) t

end TDA.Persistence
