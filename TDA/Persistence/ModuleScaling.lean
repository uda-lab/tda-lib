import TDA.Persistence.RealInterleavingDistance
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Data.ENNReal.Inv

/-!
# Positive scaling of real persistence modules

Positive scaling of real persistence modules is reindexing by `t ↦ c⁻¹ * t`.  The
interleaving scaling law below is a library extension proved from the merged definitions,
using the conventions of BL15-v4 §3.1; no external theorem is translated.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory RealShift
open scoped NNReal ENNReal

variable {R : Type u} [Ring R]

private def reindexIso {a b : ℝ →o ℝ} (h : ∀ t, a t = b t)
    (M : PModule.{u,0,w} R ℝ) : reindex a M ≅ reindex b M :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun t => eqToIso (h t)) (by intros; apply Subsingleton.elim)) M

namespace PModule

/-- The order hom used to scale a real persistence module by `c > 0`. -/
noncomputable def scaleHom (c : ℝ) (hc : 0 < c) : ℝ →o ℝ :=
  (OrderIso.mulLeft₀ c⁻¹ (inv_pos.2 hc)).toOrderEmbedding.toOrderHom

/-- Scaling reindexes a module at `t` by the original parameter `c⁻¹ * t`. -/
@[simp] theorem scaleHom_apply (c : ℝ) (hc : 0 < c) (t : ℝ) :
    scaleHom c hc t = c⁻¹ * t := rfl

/-- The positive scaling of a real persistence module. -/
noncomputable def scale (c : ℝ) (hc : 0 < c) (M : PModule.{u,0,w} R ℝ) :
    PModule.{u,0,w} R ℝ :=
  reindex (scaleHom c hc) M

/-- The object of a scaled module at `t` is the original object at `c⁻¹ * t`. -/
@[simp] theorem scale_obj (c : ℝ) (hc : 0 < c) (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (scale c hc M).obj t = M.obj (c⁻¹ * t) := rfl

/-- Scaling preserves the original structure map at the reindexed inequality. -/
theorem structureMap_scale (c : ℝ) (hc : 0 < c) (M : PModule.{u,0,w} R ℝ)
    {s t : ℝ} (h : s ≤ t) :
    structureMap (scale c hc M) h =
      structureMap M ((scaleHom c hc).monotone h) := rfl

/-- Scaling acts functorially on real persistence modules. -/
noncomputable def scaleFunctor (c : ℝ) (hc : 0 < c) :
    PModule.{u,0,w} R ℝ ⥤ PModule.{u,0,w} R ℝ where
  obj M := scale c hc M
  map f := reindexNatTrans (scaleHom c hc) f
  map_id M := reindexNatTrans_id (scaleHom c hc) M
  map_comp f g := reindexNatTrans_comp (scaleHom c hc) f g

private theorem scaleOneIndex (t : ℝ) : scaleHom 1 one_pos t = t := by
  simp [scaleHom]

private theorem scaleScaleIndex (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    (scaleHom a ha).comp (scaleHom b hb) t = scaleHom (b * a) (mul_pos hb ha) t := by
  change a⁻¹ * (b⁻¹ * t) = (b * a)⁻¹ * t
  rw [mul_inv_rev]
  exact (mul_assoc _ _ _).symm

private theorem scaleInvIndex (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (scaleHom c hc).comp (scaleHom c⁻¹ (inv_pos.2 hc)) t = t := by
  change c⁻¹ * ((c⁻¹)⁻¹ * t) = t
  rw [inv_inv, inv_mul_cancel_left₀ hc.ne']

private theorem scaleShiftIndex (c : ℝ) (hc : 0 < c) (ε : ℝ≥0) (t : ℝ) :
    scaleHom c hc (t + ((Real.toNNReal c * ε : ℝ≥0) : ℝ)) =
      scaleHom c hc t + (ε : ℝ) := by
  rw [scaleHom_apply, scaleHom_apply]
  calc
    c⁻¹ * (t + ((Real.toNNReal c * ε : ℝ≥0) : ℝ)) =
        c⁻¹ * (t + c * (ε : ℝ)) := by
      congr 1
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ hc.le]
    _ = c⁻¹ * t + c⁻¹ * (c * (ε : ℝ)) := by rw [mul_add]
    _ = c⁻¹ * t + (ε : ℝ) := by rw [inv_mul_cancel_left₀ hc.ne']

private theorem scaleOneIndex' (t : ℝ) :
    (scaleHom 1 one_pos).comp (OrderHom.id : ℝ →o ℝ) t = t := by
  simp

private theorem scaleScaleIndex' (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    (scaleHom a ha).comp (scaleHom b hb) t =
      scaleHom (b * a) (mul_pos hb ha) t := scaleScaleIndex a b ha hb t

private theorem scaleInvIndex' (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (scaleHom c hc).comp (scaleHom c⁻¹ (inv_pos.2 hc)) t =
      (OrderHom.id : ℝ →o ℝ) t := by
  simpa using scaleInvIndex c hc t

private theorem scaleShiftIndex' (c : ℝ) (hc : 0 < c) (ε : ℝ≥0) (t : ℝ) :
    (scaleHom c hc).comp (translation (Real.toNNReal c * ε)) t =
      (translation ε).comp (scaleHom c hc) t := by
  exact scaleShiftIndex c hc ε t

/-- The scaling unit at factor one. -/
noncomputable def scaleOneIso (M : PModule.{u,0,w} R ℝ) : scale 1 one_pos M ≅ M := by
  change reindex (scaleHom 1 one_pos) M ≅ reindex (OrderHom.id : ℝ →o ℝ) M
  exact reindexIso scaleOneIndex' M

/-- The component of the scaling unit is transport along `1⁻¹ * t = t`. -/
@[simp] theorem scaleOneIso_hom_app (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (scaleOneIso M).hom.app t = M.map (eqToHom (scaleOneIndex t)) := rfl

/-- The scaling unit is natural in the module. -/
theorem scaleOneIso_naturality {M N : PModule.{u,0,w} R ℝ} (f : M ⟶ N) :
    reindexNatTrans (scaleHom 1 one_pos) f ≫ (scaleOneIso N).hom =
      (scaleOneIso M).hom ≫ f := by
  apply NatTrans.ext
  funext t
  exact (f.naturality (eqToHom (scaleOneIndex t))).symm

/-- The coherence isomorphism for two successive positive scalings. -/
noncomputable def scaleScaleIso (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (M : PModule.{u,0,w} R ℝ) :
    scale b hb (scale a ha M) ≅ scale (b * a) (mul_pos hb ha) M := by
  change reindex (scaleHom b hb) (reindex (scaleHom a ha) M) ≅
    reindex (scaleHom (b * a) (mul_pos hb ha)) M
  exact reindexIso (scaleScaleIndex' a b ha hb) M

/-- The component of successive scaling coherence is transport along the composite index equality. -/
@[simp] theorem scaleScaleIso_hom_app (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (scaleScaleIso a b ha hb M).hom.app t =
      M.map (eqToHom (scaleScaleIndex a b ha hb t)) := rfl

/-- Successive scaling coherence is natural in the module. -/
theorem scaleScaleIso_naturality (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {M N : PModule.{u,0,w} R ℝ} (f : M ⟶ N) :
    reindexNatTrans (scaleHom b hb) (reindexNatTrans (scaleHom a ha) f) ≫
        (scaleScaleIso a b ha hb N).hom =
      (scaleScaleIso a b ha hb M).hom ≫
        reindexNatTrans (scaleHom (b * a) (mul_pos hb ha)) f := by
  apply NatTrans.ext
  funext t
  exact (f.naturality (eqToHom (scaleScaleIndex a b ha hb t))).symm

/-- The coherence isomorphism identifying scaling by `c` and then by `c⁻¹` with the original module. -/
noncomputable def scaleInvIso {c : ℝ} (hc : 0 < c) (M : PModule.{u,0,w} R ℝ) :
    scale c⁻¹ (inv_pos.2 hc) (scale c hc M) ≅ M := by
  change reindex (scaleHom c⁻¹ (inv_pos.2 hc)) (reindex (scaleHom c hc) M) ≅
    reindex (OrderHom.id : ℝ →o ℝ) M
  exact reindexIso (scaleInvIndex' c hc) M

/-- The inverse-scaling component is transport along `c⁻¹ * (c * t) = t`. -/
@[simp] theorem scaleInvIso_hom_app {c : ℝ} (hc : 0 < c)
    (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (scaleInvIso hc M).hom.app t = M.map (eqToHom (scaleInvIndex c hc t)) := rfl

/-- Inverse-scaling coherence is natural in the module. -/
theorem scaleInvIso_naturality {c : ℝ} (hc : 0 < c)
    {M N : PModule.{u,0,w} R ℝ} (f : M ⟶ N) :
    reindexNatTrans (scaleHom c⁻¹ (inv_pos.2 hc))
        (reindexNatTrans (scaleHom c hc) f) ≫ (scaleInvIso hc N).hom =
      (scaleInvIso hc M).hom ≫ f := by
  apply NatTrans.ext
  funext t
  exact (f.naturality (eqToHom (scaleInvIndex c hc t))).symm

/-- The canonical comparison between scaling after a shift and shifting after scaling. -/
noncomputable def scaleShiftIso (c : ℝ) (hc : 0 < c) (ε : ℝ≥0)
    (M : PModule.{u,0,w} R ℝ) :
    (shift (Real.toNNReal c * ε)).obj (scale c hc M) ≅
      scale c hc ((shift ε).obj M) := by
  change reindex (translation (Real.toNNReal c * ε))
      (reindex (scaleHom c hc) M) ≅
    reindex (scaleHom c hc) (reindex (translation ε) M)
  exact reindexIso (scaleShiftIndex' c hc ε) M

/-- The shift-comparison component is transport along `c⁻¹(t+cε)=c⁻¹t+ε`. -/
@[simp] theorem scaleShiftIso_hom_app (c : ℝ) (hc : 0 < c) (ε : ℝ≥0)
    (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (scaleShiftIso c hc ε M).hom.app t =
      M.map (eqToHom (scaleShiftIndex c hc ε t)) := rfl

private theorem scaleShiftIso_inv_app (c : ℝ) (hc : 0 < c) (ε : ℝ≥0)
    (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (scaleShiftIso c hc ε M).inv.app t =
      M.map (eqToHom (scaleShiftIndex c hc ε t).symm) := rfl

/-- The shift comparison is natural in the module. -/
theorem scaleShiftIso_naturality (c : ℝ) (hc : 0 < c) (ε : ℝ≥0)
    {M N : PModule.{u,0,w} R ℝ} (f : M ⟶ N) :
    (shift (Real.toNNReal c * ε)).map (reindexNatTrans (scaleHom c hc) f) ≫
        (scaleShiftIso c hc ε N).hom =
      (scaleShiftIso c hc ε M).hom ≫
        reindexNatTrans (scaleHom c hc) ((shift ε).map f) := by
  apply NatTrans.ext
  funext t
  exact (f.naturality (eqToHom (scaleShiftIndex c hc ε t))).symm

end PModule

namespace RealInterleaving

variable {ε : ℝ≥0} {M N : PModule.{u,0,w} R ℝ}

private theorem scale_equation (i : RealInterleaving ε M N) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (reindexNatTrans (PModule.scaleHom c hc) i.φ ≫
        (PModule.scaleShiftIso c hc ε N).inv).app t ≫
      (reindexNatTrans (PModule.scaleHom c hc) i.ψ ≫
        (PModule.scaleShiftIso c hc ε M).inv).app
        (t + ((Real.toNNReal c * ε : ℝ≥0) : ℝ)) ≫
      (compIso (Real.toNNReal c * ε) (Real.toNNReal c * ε)
        (PModule.scale c hc M)).hom.app t =
    (transition (Real.toNNReal c * ε + Real.toNNReal c * ε)
      (PModule.scale c hc M)).app t := by
  change
    i.φ.app (PModule.scaleHom c hc t) ≫
        (PModule.scaleShiftIso c hc ε N).inv.app t ≫
      i.ψ.app (PModule.scaleHom c hc
        (t + ((Real.toNNReal c * ε : ℝ≥0) : ℝ))) ≫
        (PModule.scaleShiftIso c hc ε M).inv.app
          (t + ((Real.toNNReal c * ε : ℝ≥0) : ℝ)) ≫
      (compIso (Real.toNNReal c * ε) (Real.toNNReal c * ε)
        (PModule.scale c hc M)).hom.app t =
    (transition (Real.toNNReal c * ε + Real.toNNReal c * ε)
      (PModule.scale c hc M)).app t
  rw [PModule.scaleShiftIso_inv_app, PModule.scaleShiftIso_inv_app]
  simp only [compIso_hom_app, transition_app]
  erw [i.ψ.naturality_assoc]
  erw [← Category.assoc (i.φ.app (PModule.scaleHom c hc t))
    (i.ψ.app (PModule.scaleHom c hc t + (ε : ℝ))), i.φ_ψ_structureMap]
  change M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  repeat' erw [← M.map_comp]
  congr 1

/-- Scale an interleaving by a positive real factor, multiplying its parameter by that factor. -/
noncomputable def scale (i : RealInterleaving ε M N) (c : ℝ) (hc : 0 < c) :
    RealInterleaving (Real.toNNReal c * ε) (PModule.scale c hc M) (PModule.scale c hc N) :=
  ofApp
    (reindexNatTrans (PModule.scaleHom c hc) i.φ ≫
      (PModule.scaleShiftIso c hc ε N).inv)
    (reindexNatTrans (PModule.scaleHom c hc) i.ψ ≫
      (PModule.scaleShiftIso c hc ε M).inv)
    (scale_equation i c hc)
    (scale_equation i.symm c hc)

/-- The first component of a scaled interleaving is the reindexed original component followed by
the inverse shift comparison. -/
@[simp] theorem scale_φ_app (i : RealInterleaving ε M N) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (i.scale c hc).φ.app t =
      i.φ.app (PModule.scaleHom c hc t) ≫
        (PModule.scaleShiftIso c hc ε N).inv.app t := rfl

/-- The second component of a scaled interleaving is the reindexed original component followed by
the inverse shift comparison. -/
@[simp] theorem scale_ψ_app (i : RealInterleaving ε M N) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (i.scale c hc).ψ.app t =
      i.ψ.app (PModule.scaleHom c hc t) ≫
        (PModule.scaleShiftIso c hc ε M).inv.app t := rfl

end RealInterleaving

variable {M N : PModule.{u,0,w} R ℝ}

/-- A finite-parameter interleaving exists after positive scaling exactly when it existed before. -/
theorem nonempty_realInterleaving_scale_iff (c : ℝ) (hc : 0 < c) (ε : ℝ≥0) :
    Nonempty (RealInterleaving (Real.toNNReal c * ε)
      (PModule.scale c hc M) (PModule.scale c hc N)) ↔
      Nonempty (RealInterleaving ε M N) := by
  constructor
  · rintro ⟨i⟩
    have j := i.scale c⁻¹ (inv_pos.2 hc)
    have h : Real.toNNReal c⁻¹ * (Real.toNNReal c * ε) = ε := by
      rw [← mul_assoc, ← Real.toNNReal_mul (inv_nonneg.2 hc.le),
        inv_mul_cancel₀ hc.ne', Real.toNNReal_one, one_mul]
    have j' := j.congr (PModule.scaleInvIso hc M) (PModule.scaleInvIso hc N)
    rw [h] at j'
    exact ⟨j'⟩
  · rintro ⟨i⟩
    exact ⟨i.scale c hc⟩

/-- Positive scaling multiplies the real interleaving distance by `ENNReal.ofReal c`, including
the case where the distance is infinite. -/
theorem realInterleavingDistance_scale (c : ℝ) (hc : 0 < c)
    (M N : PModule.{u,0,w} R ℝ) :
    realInterleavingDistance (PModule.scale c hc M) (PModule.scale c hc N) =
      ENNReal.ofReal c * realInterleavingDistance M N := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  apply le_antisymm
  · calc
      realInterleavingDistance (PModule.scale c hc M) (PModule.scale c hc N) ≤
          ⨅ (ε : ℝ≥0) (_ : Nonempty (RealInterleaving ε M N)),
            ENNReal.ofReal c * (ε : ℝ≥0∞) := by
        refine le_iInf fun ε => le_iInf fun hε => ?_
        obtain ⟨i⟩ := hε
        change realInterleavingDistance (PModule.scale c hc M) (PModule.scale c hc N) ≤
          (Real.toNNReal c : ℝ≥0∞) * (ε : ℝ≥0∞)
        rw [← ENNReal.coe_mul]
        exact RealInterleaving.distance_le (i.scale c hc)
    _ = ENNReal.ofReal c * realInterleavingDistance M N := by
      symm
      simp only [realInterleavingDistance,
        ENNReal.mul_iInf_of_ne hc0 hct]
  · refine le_iInf₂ fun δ hδ => ?_
    obtain ⟨j⟩ := hδ
    have hback : Nonempty (RealInterleaving (Real.toNNReal c⁻¹ * δ) M N) := by
      have j' := j.scale c⁻¹ (inv_pos.2 hc)
      have j'' := j'.congr (PModule.scaleInvIso hc M) (PModule.scaleInvIso hc N)
      exact ⟨j''⟩
    have hdist := RealInterleaving.distance_le (Classical.choice hback)
    have hmul := mul_le_mul_right hdist (ENNReal.ofReal c)
    calc
      ENNReal.ofReal c * realInterleavingDistance M N ≤
          ENNReal.ofReal c * (Real.toNNReal c⁻¹ * δ : ℝ≥0∞) := hmul
      _ = (δ : ℝ≥0∞) := by
        have h : Real.toNNReal c * Real.toNNReal c⁻¹ = 1 := by
          rw [← Real.toNNReal_mul hc.le, mul_inv_cancel₀ hc.ne', Real.toNNReal_one]
        change ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) *
            ((Real.toNNReal c⁻¹ * δ : ℝ≥0) : ℝ≥0∞) = δ
        rw [← ENNReal.coe_mul, ← mul_assoc, h, one_mul]

/-- The positive-scaling distance law preserves whether the distance is infinite. -/
theorem realInterleavingDistance_scale_eq_top_iff (c : ℝ) (hc : 0 < c)
    (M N : PModule.{u,0,w} R ℝ) :
    realInterleavingDistance (PModule.scale c hc M) (PModule.scale c hc N) = ⊤ ↔
      realInterleavingDistance M N = ⊤ := by
  rw [realInterleavingDistance_scale c hc M N]
  simp [ENNReal.mul_eq_top, (ENNReal.ofReal_pos.2 hc).ne', ENNReal.ofReal_ne_top]

end TDA.Persistence
