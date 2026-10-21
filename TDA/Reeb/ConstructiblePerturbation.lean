import TDA.Reeb.ConstructibleGeometricInterleaving
import TDA.Reeb.GeometricDistanceBounds
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Level changes of a fixed cylinder presentation

Affine reparametrization on each segment, together with the identity on the vertex
pieces, induces a homeomorphism between realizations of the same presentation at
two strictly increasing level lists. The transported height differs by at most
the sup distance between those lists. No compactness or local connectedness is
needed for these carrier-level constructions.
-/

set_option autoImplicit false

open Set Topology

universe u

namespace TDA.Reeb.CylinderPresentation

noncomputable section

variable {n : ℕ} (S T : CriticalValues n)

/-- The affine reparametrization of a segment preserving the endpoint correspondence. -/
def segMap (e : Fin n) : C(Seg S e, Seg T e) :=
  ⟨fun t => ⟨T.value e.castSucc +
      ((t : ℝ) - S.value e.castSucc) / (S.value e.succ - S.value e.castSucc) *
        (T.value e.succ - T.value e.castSucc), by
    have hs := sub_pos.mpr (S.value_castSucc_lt_succ e)
    have ht := sub_pos.mpr (T.value_castSucc_lt_succ e)
    have hweight0 : 0 ≤ ((t : ℝ) - S.value e.castSucc) /
        (S.value e.succ - S.value e.castSucc) := div_nonneg (sub_nonneg.mpr t.2.1) hs.le
    have hweight1 : ((t : ℝ) - S.value e.castSucc) /
        (S.value e.succ - S.value e.castSucc) ≤ 1 := (div_le_one hs).mpr (by linarith [t.2.2])
    constructor <;> nlinarith⟩, by
    fun_prop⟩

@[simp] theorem segMap_segBot (e : Fin n) : segMap S T e (segBot S e) = segBot T e := by
  apply Subtype.ext
  simp [segMap, segBot]

@[simp] theorem segMap_segTop (e : Fin n) : segMap S T e (segTop S e) = segTop T e := by
  apply Subtype.ext
  have hs : S.value e.succ - S.value e.castSucc ≠ 0 :=
    (sub_pos.mpr (S.value_castSucc_lt_succ e)).ne'
  simp [segMap, segTop, hs]

/-- Reparametrizing back to the original levels fixes every segment point. -/
@[simp] theorem segMap_segMap (e : Fin n) (t : Seg S e) :
    segMap T S e (segMap S T e t) = t := by
  apply Subtype.ext
  have hs : S.value e.succ - S.value e.castSucc ≠ 0 :=
    (sub_pos.mpr (S.value_castSucc_lt_succ e)).ne'
  have ht : T.value e.succ - T.value e.castSucc ≠ 0 :=
    (sub_pos.mpr (T.value_castSucc_lt_succ e)).ne'
  change S.value e.castSucc +
    (T.value e.castSucc + ((t : ℝ) - S.value e.castSucc) /
      (S.value e.succ - S.value e.castSucc) * (T.value e.succ - T.value e.castSucc) -
      T.value e.castSucc) / (T.value e.succ - T.value e.castSucc) *
      (S.value e.succ - S.value e.castSucc) = t
  field_simp
  ring

@[simp] theorem segMap_self (e : Fin n) (t : Seg S e) : segMap S S e t = t := by
  apply Subtype.ext
  have hs : S.value e.succ - S.value e.castSucc ≠ 0 :=
    (sub_pos.mpr (S.value_castSucc_lt_succ e)).ne'
  change S.value e.castSucc + ((t : ℝ) - S.value e.castSucc) /
    (S.value e.succ - S.value e.castSucc) * (S.value e.succ - S.value e.castSucc) = t
  rw [div_mul_cancel₀ _ hs]
  ring

/-- A segment point moves by at most the larger endpoint displacement. -/
theorem abs_sub_segMap_le (e : Fin n) (t : Seg S e) :
    |(t : ℝ) - segMap S T e t| ≤
      max |S.value e.castSucc - T.value e.castSucc| |S.value e.succ - T.value e.succ| := by
  let weight := ((t : ℝ) - S.value e.castSucc) / (S.value e.succ - S.value e.castSucc)
  have hs := sub_pos.mpr (S.value_castSucc_lt_succ e)
  have hweight0 : 0 ≤ weight := div_nonneg (sub_nonneg.mpr t.2.1) hs.le
  have hweight1 : weight ≤ 1 := (div_le_one hs).mpr (by linarith [t.2.2])
  have ha := abs_le.mp (le_max_left |S.value e.castSucc - T.value e.castSucc|
    |S.value e.succ - T.value e.succ|)
  have hb := abs_le.mp (le_max_right |S.value e.castSucc - T.value e.castSucc|
    |S.value e.succ - T.value e.succ|)
  have hformula : (t : ℝ) - segMap S T e t =
      (1 - weight) * (S.value e.castSucc - T.value e.castSucc) +
        weight * (S.value e.succ - T.value e.succ) := by
    change (t : ℝ) - (T.value e.castSucc + weight * (T.value e.succ - T.value e.castSucc)) = _
    dsimp [weight]
    field_simp
    ring
  rw [hformula]
  have hweight : 0 ≤ 1 - weight := sub_nonneg.mpr hweight1
  have ha₁ := mul_le_mul_of_nonneg_left ha.1 hweight
  have ha₂ := mul_le_mul_of_nonneg_left ha.2 hweight
  have hb₁ := mul_le_mul_of_nonneg_left hb.1 hweight0
  have hb₂ := mul_le_mul_of_nonneg_left hb.2 hweight0
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

variable (P : CylinderPresentation.{u} n)

/-- Identity on vertex pieces and affine reparametrization on cylinders, descended by `lift`. -/
def levelMap : C(P.Realization S, P.Realization T) :=
  lift
    { vertex i := ⟨P.ofVertex T i, P.continuous_ofVertex T i⟩
      cylinder e := (⟨P.ofCylinder T e, P.continuous_ofCylinder T e⟩ :
        C(P.Cylinder T e, P.Realization T)).comp
          (ContinuousMap.prodMap (ContinuousMap.id _) (segMap S T e))
      segBot_eq e y := by simp [ContinuousMap.prodMap, P.ofCylinder_segBot]
      segTop_eq e y := by simp [ContinuousMap.prodMap, P.ofCylinder_segTop] }

@[simp] theorem levelMap_ofVertex (i : Fin (n + 1)) (v : P.V i) :
    P.levelMap S T (P.ofVertex S i v) = P.ofVertex T i v := rfl

@[simp] theorem levelMap_ofCylinder (e : Fin n) (p : P.Cylinder S e) :
    P.levelMap S T (P.ofCylinder S e p) = P.ofCylinder T e (p.1, segMap S T e p.2) := rfl

/-- The reverse change of levels is inverse on the entire quotient. -/
@[simp] theorem levelMap_levelMap (q : P.Realization S) :
    P.levelMap T S (P.levelMap S T q) = q := by
  have h : (P.levelMap T S).comp (P.levelMap S T) = ContinuousMap.id _ := by
    apply hom_ext
    · intro i v
      simp
    · intro e p
      simp
  exact congrArg (fun f : C(P.Realization S, P.Realization S) => f q) h

@[simp] theorem levelMap_self : P.levelMap S S = ContinuousMap.id _ := by
  apply hom_ext
  · intro i v; simp
  · intro e p; simp

/-- Changing levels of a fixed presentation gives a homeomorphism of realizations. -/
def levelHomeomorph : P.Realization S ≃ₜ P.Realization T where
  toFun := P.levelMap S T
  invFun := P.levelMap T S
  left_inv := P.levelMap_levelMap S T
  right_inv := P.levelMap_levelMap T S
  continuous_toFun := (P.levelMap S T).continuous
  continuous_invFun := (P.levelMap T S).continuous

@[simp] theorem levelHomeomorph_apply (q : P.Realization S) :
    P.levelHomeomorph S T q = P.levelMap S T q := rfl

/-- Pointwise height displacement is bounded by the sup distance of the level lists. -/
theorem abs_height_sub_height_levelMap_le (q : P.Realization S) :
    |P.height S q - P.height T (P.levelMap S T q)| ≤ dist S.value T.value := by
  obtain ⟨x, rfl⟩ := P.quotMk_surjective S q
  rcases x with ⟨i, v⟩ | ⟨e, y, t⟩
  · change |P.height S (P.ofVertex S i v) -
      P.height T (P.levelMap S T (P.ofVertex S i v))| ≤ _
    simpa only [levelMap_ofVertex, height_ofVertex, Real.dist_eq] using
      dist_le_pi_dist S.value T.value i
  · change |P.height S (P.ofCylinder S e (y, t)) -
      P.height T (P.levelMap S T (P.ofCylinder S e (y, t)))| ≤ _
    simp only [levelMap_ofCylinder, height_ofCylinder]
    exact (abs_sub_segMap_le S T e t).trans (max_le
      (by simpa only [Real.dist_eq] using dist_le_pi_dist S.value T.value e.castSucc)
      (by simpa only [Real.dist_eq] using dist_le_pi_dist S.value T.value e.succ))

/-- The transported height is within the sup extended distance of the level lists. -/
theorem edist_height_levelMap_le :
    edist (UniformFun.ofFun ⇑(P.height S))
        (UniformFun.ofFun ⇑((P.height T).comp (P.levelMap S T))) ≤ edist S.value T.value := by
  apply UniformFun.edist_le.mpr
  intro q
  simpa only [UniformFun.toFun_ofFun, ContinuousMap.comp_apply, edist_dist, Real.dist_eq] using
    ENNReal.ofReal_le_ofReal (P.abs_height_sub_height_levelMap_le S T q)

end

end TDA.Reeb.CylinderPresentation
