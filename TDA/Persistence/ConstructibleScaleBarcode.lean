import TDA.Persistence.ModuleScaling
import TDA.Persistence.ConstructibleIsometry
import TDA.Persistence.ConstructibleShiftBarcode
import TDA.Persistence.DiagramBottleneckScaling

/-!
# Positive scaling of finite-constructible module diagrams

Positive scaling transports the critical grid and the finite-constructible barcode of a real
persistence module. The diagram formula and its bottleneck consequence are library extensions
proved from the merged constructible-module and diagram definitions.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory
open CategoryTheory.Limits
open scoped Classical ENNReal

variable {n m : ℕ}

variable {R : Type u} [Ring R]
variable {g : Fin n ↪o ℝ} {M : PModule.{u,0,w} R ℝ}

/-! ### Scaled grids and constructibility -/

/- The grid transport is deliberately defined by the order-isomorphism map, so its application
   theorem is definitionally the stated multiplication formula. -/
/-- Scale every critical value of a finite grid by a positive real factor. -/
noncomputable def scaleGrid (c : ℝ) (hc : 0 < c) (g : Fin n ↪o ℝ) : Fin n ↪o ℝ :=
  g.trans (OrderIso.mulLeft₀ c hc).toOrderEmbedding

/-- The scaled grid evaluates to `c * g i`. -/
@[simp] theorem scaleGrid_apply (c : ℝ) (hc : 0 < c) (g : Fin n ↪o ℝ) (i : Fin n) :
    scaleGrid c hc g i = c * g i := rfl

/-- Cell indices on a scaled grid are the original cell indices at the inverse-scaled parameter. -/
theorem cellIndex_scaleGrid (c : ℝ) (hc : 0 < c) (g : Fin n ↪o ℝ) (t : ℝ) :
    cellIndex (scaleGrid c hc g) t = cellIndex g (c⁻¹ * t) := by
  apply Fin.ext
  change (Finset.univ.filter (fun i => c * g i ≤ t)).card =
    (Finset.univ.filter (fun i => g i ≤ c⁻¹ * t)).card
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (le_inv_mul_iff₀ hc).symm

/-- Positive scaling preserves finite constructibility on the scaled critical grid. -/
theorem IsConstructible.scale {g : Fin n ↪o ℝ} {M : PModule.{u,0,w} R ℝ}
    (hM : IsConstructible g M) (c : ℝ) (hc : 0 < c) :
    IsConstructible (scaleGrid c hc g) (PModule.scale c hc M) where
  zero_left t ht := by
    change IsZero (M.obj (c⁻¹ * t))
    apply hM.zero_left (c⁻¹ * t)
    intro i
    exact (inv_mul_lt_iff₀ hc).2 (by simpa only [scaleGrid_apply] using ht i)
  isIso_map s t hst hd := by
    change IsIso (structureMap M ((PModule.scaleHom c hc).monotone hst))
    apply hM.isIso_map
    rw [cellIndex_scaleGrid, cellIndex_scaleGrid] at hd
    exact hd

/-! ### Critical restrictions and endpoint transport -/

/-- The scaled critical restriction is isomorphic to the original critical restriction. -/
noncomputable def scaledCriticalIso (g : Fin n ↪o ℝ) (M : PModule.{u,0,w} R ℝ) (c : ℝ) (hc : 0 < c) :
    reindex (scaleGrid c hc g).toOrderHom (PModule.scale c hc M) ≅
      reindex g.toOrderHom M := by
  let e : ((PModule.scaleHom c hc).comp (scaleGrid c hc g).toOrderHom).toFunctor ≅
      g.toOrderHom.toFunctor :=
    NatIso.ofComponents (fun i => eqToIso (inv_mul_cancel_left₀ hc.ne' (g i)))
      (by intros; apply Subsingleton.elim)
  exact Functor.isoWhiskerRight e M

variable {k : Type u} [Field k]

/-- Finite-dimensionality at the original critical fibers is preserved by scaled restriction. -/
theorem finiteDimensional_scaledCritical {g : Fin n ↪o ℝ}
    {M : PModule.{u,0,u} k ℝ}
    (hfd : ∀ i, FiniteDimensional k (M.obj (g i))) (c : ℝ) (hc : 0 < c) (i : Fin n) :
    FiniteDimensional k ((PModule.scale c hc M).obj (scaleGrid c hc g i)) := by
  change FiniteDimensional k (M.obj (c⁻¹ * (c * g i)))
  rw [inv_mul_cancel_left₀ hc.ne']
  exact hfd i

private theorem endpoints_scale (g : Fin n ↪o ℝ) (c : ℝ) (hc : 0 < c)
    (I : FiniteInterval n) :
    RealBarcode.endpoints (scaleGrid c hc g) I =
      (c * (RealBarcode.endpoints g I).1,
        WithTop.map (c * ·) (RealBarcode.endpoints g I).2) := by
  dsimp only [RealBarcode.endpoints]
  split_ifs <;> simp [scaleGrid_apply]

/-- Relabeling index bars on a scaled grid scales every real barcode endpoint. -/
theorem ofIndexBars_scaleGrid (g : Fin n ↪o ℝ) (c : ℝ) (hc : 0 < c)
    (B : Multiset (FiniteInterval n)) :
    ofIndexBars (scaleGrid c hc g) (scaleGrid c hc g).strictMono B =
      (ofIndexBars g g.strictMono B).scale c hc := by
  apply Diagram.ext
  change B.map (RealBarcode.endpoints (scaleGrid c hc g)) =
    (B.map (RealBarcode.endpoints g)).map
      (fun p => (c * p.1, WithTop.map (c * ·) p.2))
  rw [Multiset.map_map]
  congr 1
  funext I
  exact endpoints_scale g c hc I

/-! ### The module diagram formula -/

/-- The diagram of a scaled module on its scaled grid is the scaled original diagram. -/
theorem moduleDiagram_scale (g : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (g i))) (c : ℝ) (hc : 0 < c) :
    moduleDiagram (scaleGrid c hc g) (PModule.scale c hc M)
        (finiteDimensional_scaledCritical hfd c hc) =
      (moduleDiagram g M hfd).scale c hc := by
  let : ∀ i, FiniteDimensional k ((reindex g.toOrderHom M).obj i) := hfd
  let : ∀ i, FiniteDimensional k
      ((reindex (scaleGrid c hc g).toOrderHom (PModule.scale c hc M)).obj i) :=
    finiteDimensional_scaledCritical hfd c hc
  unfold moduleDiagram
  rw [rankBarcode_eq_of_iso (scaledCriticalIso g M c hc), ofIndexBars_scaleGrid]

/-- The bottleneck distance of scaled finite-constructible module diagrams obeys the exact
interleaving-distance scaling law. -/
theorem bottleneck_moduleDiagram_scale
    {g : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}
    {M : PModule.{u,0,u} k ℝ} {N : PModule.{u,0,u} k ℝ}
    (hM : IsConstructible g M) (hN : IsConstructible d N)
    (hfdM : ∀ j, FiniteDimensional k (M.obj (g j)))
    (hfdN : ∀ j, FiniteDimensional k (N.obj (d j))) (c : ℝ) (hc : 0 < c) :
    bottleneck
        (moduleDiagram (scaleGrid c hc g) (PModule.scale c hc M)
          (finiteDimensional_scaledCritical hfdM c hc))
        (moduleDiagram (scaleGrid c hc d) (PModule.scale c hc N)
          (finiteDimensional_scaledCritical hfdN c hc)) =
      ENNReal.ofReal c * realInterleavingDistance M N := by
  calc
    bottleneck
        (moduleDiagram (scaleGrid c hc g) (PModule.scale c hc M)
          (finiteDimensional_scaledCritical hfdM c hc))
        (moduleDiagram (scaleGrid c hc d) (PModule.scale c hc N)
          (finiteDimensional_scaledCritical hfdN c hc)) =
        bottleneck ((moduleDiagram g M hfdM).scale c hc)
          ((moduleDiagram d N hfdN).scale c hc) := by
            rw [moduleDiagram_scale, moduleDiagram_scale]
    _ = ENNReal.ofReal c * bottleneck (moduleDiagram g M hfdM)
          (moduleDiagram d N hfdN) := bottleneck_scale _ _ hc
    _ = ENNReal.ofReal c * realInterleavingDistance M N := by
      rw [bottleneck_eq_distance hM hN hfdM hfdN]

end TDA.Persistence.FiniteConstructible
