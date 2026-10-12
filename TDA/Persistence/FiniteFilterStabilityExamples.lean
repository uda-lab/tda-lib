import TDA.Persistence.FaceOrderTemplate
import TDA.Filtration.CompatibleOrderExistence
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-! A triangle-boundary family in which the two first edge grades exchange order. -/

namespace TDA.Persistence.Examples
open TDA.Simplicial TDA.Filtration TDA.Persistence

private def triangleBoundary : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s.card ≤ 2}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, (Finset.card_le_card hts).trans hs.2⟩

private instance triangleBoundaryFaces :
    Fintype (TotalFace triangleBoundary) := by
  change Fintype {s : Finset (Fin 3) // s.Nonempty ∧ s.card ≤ 2}
  infer_instance

private theorem triangleBoundary_faceCount : faceCount triangleBoundary = 6 := by decide

private def triangleValue (t : Set.Icc (0 : ℝ) 1)
    (s : TotalFace triangleBoundary) : ℝ :=
  if s.1.card = 1 then
    if (0 : Fin 3) ∈ s.1 then 0 else if (1 : Fin 3) ∈ s.1 then 2 else 1
  else if (0 : Fin 3) ∈ s.1 ∧ (1 : Fin 3) ∈ s.1 then 3 + t.1
  else if (1 : Fin 3) ∈ s.1 ∧ (2 : Fin 3) ∈ s.1 then 4 - t.1
  else 5

private theorem triangleValue_mono (t : Set.Icc (0 : ℝ) 1)
    {a b : TotalFace triangleBoundary} (h : a.1 ⊆ b.1) :
    triangleValue t a ≤ triangleValue t b := by
  have h0 := t.2.1
  have h1 := t.2.2
  have classify : ∀ s : Finset (Fin 3), s.Nonempty → s.card ≤ 2 →
      s = {0} ∨ s = {1} ∨ s = {2} ∨
      s = {0, 1} ∨ s = {1, 2} ∨ s = {0, 2} := by decide
  obtain ⟨ha0, ha1⟩ := a.2
  obtain ⟨hb0, hb1⟩ := b.2
  rcases classify a.1 ha0 ha1 with ha | ha | ha | ha | ha | ha <;>
    rcases classify b.1 hb0 hb1 with hb | hb | hb | hb | hb | hb <;>
    simp_all [triangleValue, Finset.insert_subset_iff, Finset.singleton_subset_iff] <;>
    linarith

private def triangleFilter (t : Set.Icc (0 : ℝ) 1) :
    FilterFunction triangleBoundary ℝ where
  value := triangleValue t
  mono := triangleValue_mono t

private def triangleEdge01 : TotalFace triangleBoundary :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty ∧
    ({0, 1} : Finset (Fin 3)).card ≤ 2; decide⟩

private def triangleEdge12 : TotalFace triangleBoundary :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty ∧
    ({1, 2} : Finset (Fin 3)).card ≤ 2; decide⟩

private def triangleEdge02 : TotalFace triangleBoundary :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty ∧
    ({0, 2} : Finset (Fin 3)).card ≤ 2; decide⟩

private def triangleVertex0 : TotalFace triangleBoundary :=
  ⟨{0}, by change ({0} : Finset (Fin 3)).Nonempty ∧
    ({0} : Finset (Fin 3)).card ≤ 2; decide⟩

private def triangleVertex1 : TotalFace triangleBoundary :=
  ⟨{1}, by change ({1} : Finset (Fin 3)).Nonempty ∧
    ({1} : Finset (Fin 3)).card ≤ 2; decide⟩

private def triangleVertex2 : TotalFace triangleBoundary :=
  ⟨{2}, by change ({2} : Finset (Fin 3)).Nonempty ∧
    ({2} : Finset (Fin 3)).card ≤ 2; decide⟩

private def triangleOrder0Fun (i : Fin (faceCount triangleBoundary)) :
    TotalFace triangleBoundary :=
  if i.val = 0 then triangleVertex0
  else if i.val = 1 then triangleVertex2
  else if i.val = 2 then triangleVertex1
  else if i.val = 3 then triangleEdge01
  else if i.val = 4 then triangleEdge12
  else triangleEdge02

private def triangleOrder1Fun (i : Fin (faceCount triangleBoundary)) :
    TotalFace triangleBoundary :=
  if i.val = 0 then triangleVertex0
  else if i.val = 1 then triangleVertex2
  else if i.val = 2 then triangleVertex1
  else if i.val = 3 then triangleEdge12
  else if i.val = 4 then triangleEdge01
  else triangleEdge02

private theorem triangleOrder0Fun_bijective : Function.Bijective triangleOrder0Fun := by
  decide

private theorem triangleOrder1Fun_bijective : Function.Bijective triangleOrder1Fun := by
  decide

private noncomputable def triangleOrder0 : Fin (faceCount triangleBoundary) ≃
    TotalFace triangleBoundary :=
  Equiv.ofBijective triangleOrder0Fun triangleOrder0Fun_bijective

private noncomputable def triangleOrder1 : Fin (faceCount triangleBoundary) ≃
    TotalFace triangleBoundary :=
  Equiv.ofBijective triangleOrder1Fun triangleOrder1Fun_bijective

private theorem triangle_edge_values (t : Set.Icc (0 : ℝ) 1) :
    (triangleFilter t).value triangleEdge01 = 3 + t.1 ∧
    (triangleFilter t).value triangleEdge12 = 4 - t.1 ∧
    (triangleFilter t).value triangleEdge02 = 5 := by
  simp [triangleFilter, triangleValue, triangleEdge01, triangleEdge12, triangleEdge02]

private def triangleTime0 : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
private noncomputable def triangleTimeHalf : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by constructor <;> norm_num⟩
private def triangleTime1 : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

set_option linter.unusedSimpArgs false in
private noncomputable def triangleCompatible0 : CompatibleOrder (triangleFilter triangleTime0) where
  enum := triangleOrder0
  face_lt := by
    intro i j h
    have hh : ∀ i j : Fin (faceCount triangleBoundary),
        (triangleOrder0 i).val ⊂ (triangleOrder0 j).val → i.val < j.val := by decide
    have h' : i.val < j.val := hh i j h
    exact Fin.lt_def.mpr h'
  monotone := by
    intro i j hij
    have hv : ∀ q : Fin (faceCount triangleBoundary),
        (triangleFilter triangleTime0).value (triangleOrder0 q) = (q.val : ℝ) := by
      intro q
      fin_cases q <;>
        norm_num [triangleOrder0, triangleOrder0Fun, triangleFilter,
          triangleValue, triangleTime0, triangleVertex0, triangleVertex1,
          triangleVertex2, triangleEdge01, triangleEdge12, triangleEdge02] <;>
        simp [show (0 : Fin 3) ≠ 2 by decide,
          show (1 : Fin 3) ≠ 2 by decide,
          show ({1, 2} : Finset (Fin 3)).card ≠ 1 by decide,
          show ({0, 2} : Finset (Fin 3)).card ≠ 1 by decide]
    change (triangleFilter triangleTime0).value (triangleOrder0 i) ≤
      (triangleFilter triangleTime0).value (triangleOrder0 j)
    rw [hv i, hv j]
    exact_mod_cast (Fin.le_def.mp hij)

set_option linter.unusedSimpArgs false in
private noncomputable def triangleCompatible1 : CompatibleOrder (triangleFilter triangleTime1) where
  enum := triangleOrder1
  face_lt := by
    intro i j h
    have hh : ∀ i j : Fin (faceCount triangleBoundary),
        (triangleOrder1 i).val ⊂ (triangleOrder1 j).val → i.val < j.val := by decide
    have h' : i.val < j.val := hh i j h
    exact Fin.lt_def.mpr h'
  monotone := by
    intro i j hij
    have hv : ∀ q : Fin (faceCount triangleBoundary),
        (triangleFilter triangleTime1).value (triangleOrder1 q) = (q.val : ℝ) := by
      intro q
      fin_cases q <;>
        norm_num [triangleOrder1, triangleOrder1Fun, triangleFilter,
          triangleValue, triangleTime1, triangleVertex0, triangleVertex1,
          triangleVertex2, triangleEdge01, triangleEdge12, triangleEdge02] <;>
        simp [show (0 : Fin 3) ≠ 2 by decide,
          show (1 : Fin 3) ≠ 2 by decide,
          show ({1, 2} : Finset (Fin 3)).card ≠ 1 by decide,
          show ({0, 2} : Finset (Fin 3)).card ≠ 1 by decide]
    change (triangleFilter triangleTime1).value (triangleOrder1 i) ≤
      (triangleFilter triangleTime1).value (triangleOrder1 j)
    rw [hv i, hv j]
    exact_mod_cast (Fin.le_def.mp hij)

/-- The first two actual edge grades meet and exchange order in this filter family. -/
private theorem triangle_edge_order_crosses :
    (triangleFilter triangleTime0).value triangleEdge01 <
      (triangleFilter triangleTime0).value triangleEdge12 ∧
    (triangleFilter triangleTimeHalf).value triangleEdge01 =
      (triangleFilter triangleTimeHalf).value triangleEdge12 ∧
    (triangleFilter triangleTime1).value triangleEdge12 <
      (triangleFilter triangleTime1).value triangleEdge01 := by
  simp [triangle_edge_values, triangleTime0, triangleTimeHalf, triangleTime1]
  norm_num

/-- Every compatible enumeration reverses the two actual edges after the
crossing. This records the change of order without asserting a pairing law. -/
private theorem triangle_compatible_orders_reverse
    (e0 : CompatibleOrder (triangleFilter triangleTime0))
    (e1 : CompatibleOrder (triangleFilter triangleTime1)) :
    e0.enum.symm triangleEdge01 < e0.enum.symm triangleEdge12 ∧
    e1.enum.symm triangleEdge12 < e1.enum.symm triangleEdge01 := by
  constructor
  · apply e0.monotone.reflect_lt
    simpa only [e0.enum.apply_symm_apply, Function.comp_apply] using
      triangle_edge_order_crosses.1
  · apply e1.monotone.reflect_lt
    simpa only [e1.enum.apply_symm_apply, Function.comp_apply] using
      triangle_edge_order_crosses.2.2

/-- Every fiber of the concrete family is represented by its actual full face
template, including the crossing fiber with tied edge grades. -/
private theorem triangle_actual_diagram_template (t : Set.Icc (0 : ℝ) 1) :
    ∃ e : CompatibleOrder (triangleFilter t),
      evaluateFaceTemplate (ZMod 2) e (triangleFilter t) e.monotone 0 =
        dgm (ZMod 2) (triangleFilter t) 0 := by
  obtain ⟨e⟩ := exists_compatibleOrder (triangleFilter t)
  exact ⟨e, evaluateFaceTemplate_eq_dgm (ZMod 2) e (triangleFilter t) e.monotone 0⟩

private theorem triangle_explicit_endpoint_diagrams :
    evaluateFaceTemplate (ZMod 2) triangleCompatible0
        (triangleFilter triangleTime0) triangleCompatible0.monotone 0 =
      dgm (ZMod 2) (triangleFilter triangleTime0) 0 ∧
    evaluateFaceTemplate (ZMod 2) triangleCompatible1
        (triangleFilter triangleTime1) triangleCompatible1.monotone 0 =
      dgm (ZMod 2) (triangleFilter triangleTime1) 0 := by
  exact ⟨evaluateFaceTemplate_eq_dgm (ZMod 2) triangleCompatible0
    (triangleFilter triangleTime0) triangleCompatible0.monotone 0,
    evaluateFaceTemplate_eq_dgm (ZMod 2) triangleCompatible1
      (triangleFilter triangleTime1) triangleCompatible1.monotone 0⟩

#print axioms triangleValue_mono
#print axioms triangleBoundary_faceCount
#print axioms triangleOrder0Fun_bijective
#print axioms triangleOrder1Fun_bijective
#print axioms triangleCompatible0
#print axioms triangleCompatible1
#print axioms triangle_edge_values
#print axioms triangle_edge_order_crosses
#print axioms triangle_compatible_orders_reverse
#print axioms triangle_actual_diagram_template
#print axioms triangle_explicit_endpoint_diagrams

end TDA.Persistence.Examples
