import TDA.Persistence.FaceOrderTemplate
import TDA.Persistence.FaceEndpointUniqueness
import TDA.Persistence.FiniteFilterStability
import TDA.Simplicial.H0Augmentation
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

/-- The concrete crossing path is exactly the linear interpolation of its
endpoint filters, face by face. -/
private theorem triangle_family_values_interpolate
    (t : Set.Icc (0 : ℝ) 1) (σ : TotalFace triangleBoundary) :
    (triangleFilter t).value σ =
      (intervalFilter (triangleFilter ⟨0, by constructor <;> norm_num⟩)
        (triangleFilter ⟨1, by constructor <;> norm_num⟩) t).value σ := by
  have classify : ∀ s : Finset (Fin 3), s.Nonempty → s.card ≤ 2 →
      s = {0} ∨ s = {1} ∨ s = {2} ∨
      s = {0, 1} ∨ s = {1, 2} ∨ s = {0, 2} := by decide
  rcases σ with ⟨s, hs⟩
  rcases classify s hs.1 hs.2 with h | h | h | h | h | h <;>
    subst s <;>
    simp [intervalFilter_value, triangleFilter, triangleValue] <;>
    ring

private def triangleTime0 : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
private noncomputable def triangleTimeHalf : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by constructor <;> norm_num⟩
private def triangleTime1 : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

private theorem triangleFilter_ext
    (f g : FilterFunction triangleBoundary ℝ)
    (h : ∀ σ, f.value σ = g.value σ) : f = g := by
  cases f with
  | mk vf fm =>
    cases g with
    | mk vg gm =>
      have hv : vf = vg := funext h
      cases hv
      rfl

/-- The triangle-boundary family is the interpolation between its
endpoint filters, so the pairing regression lies on the stability path. -/
theorem triangle_family_interpolation (t : Set.Icc (0 : ℝ) 1) :
    triangleFilter t =
      intervalFilter (triangleFilter triangleTime0)
        (triangleFilter triangleTime1) t := by
  apply triangleFilter_ext
  intro σ
  simpa only [triangleTime0, triangleTime1] using
    triangle_family_values_interpolate t σ

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

set_option linter.unusedSimpArgs false in
private theorem triangle_half_order0_monotone :
    Monotone ((triangleFilter triangleTimeHalf).value ∘ triangleCompatible0.enum) := by
  intro i j hij
  have hv : ∀ q : Fin (faceCount triangleBoundary),
      (triangleFilter triangleTimeHalf).value (triangleOrder0 q) =
        if q.val = 3 ∨ q.val = 4 then (7 / 2 : ℝ) else q.val := by
    intro q
    fin_cases q <;>
      norm_num [triangleOrder0, triangleOrder0Fun, triangleFilter,
        triangleValue, triangleTimeHalf, triangleVertex0, triangleVertex1,
        triangleVertex2, triangleEdge01, triangleEdge12, triangleEdge02] <;>
      simp [show (0 : Fin 3) ≠ 2 by decide,
        show (1 : Fin 3) ≠ 2 by decide,
        show ({1, 2} : Finset (Fin 3)).card ≠ 1 by decide,
        show ({0, 2} : Finset (Fin 3)).card ≠ 1 by decide]
  change (triangleFilter triangleTimeHalf).value (triangleOrder0 i) ≤
    (triangleFilter triangleTimeHalf).value (triangleOrder0 j)
  rw [hv i, hv j]
  have hval : i.val ≤ j.val := Fin.le_def.mp hij
  fin_cases i <;> fin_cases j <;> norm_num at *

set_option linter.unusedSimpArgs false in
private theorem triangle_half_order1_monotone :
    Monotone ((triangleFilter triangleTimeHalf).value ∘ triangleCompatible1.enum) := by
  intro i j hij
  have hv : ∀ q : Fin (faceCount triangleBoundary),
      (triangleFilter triangleTimeHalf).value (triangleOrder1 q) =
        if q.val = 3 ∨ q.val = 4 then (7 / 2 : ℝ) else q.val := by
    intro q
    fin_cases q <;>
      norm_num [triangleOrder1, triangleOrder1Fun, triangleFilter,
        triangleValue, triangleTimeHalf, triangleVertex0, triangleVertex1,
        triangleVertex2, triangleEdge01, triangleEdge12, triangleEdge02] <;>
      simp [show (0 : Fin 3) ≠ 2 by decide,
        show (1 : Fin 3) ≠ 2 by decide,
        show ({1, 2} : Finset (Fin 3)).card ≠ 1 by decide,
        show ({0, 2} : Finset (Fin 3)).card ≠ 1 by decide]
  change (triangleFilter triangleTimeHalf).value (triangleOrder1 i) ≤
    (triangleFilter triangleTimeHalf).value (triangleOrder1 j)
  rw [hv i, hv j]
  have hval : i.val ≤ j.val := Fin.le_def.mp hij
  fin_cases i <;> fin_cases j <;> norm_num at *

private noncomputable def triangleCompatibleHalf0 :
    CompatibleOrder (triangleFilter triangleTimeHalf) :=
  triangleCompatible0.transfer triangle_half_order0_monotone

private noncomputable def triangleCompatibleHalf1 :
    CompatibleOrder (triangleFilter triangleTimeHalf) :=
  triangleCompatible1.transfer triangle_half_order1_monotone

/-- The first two edge grades meet and exchange order in this filter family. -/
private theorem triangle_edge_order_crosses :
    (triangleFilter triangleTime0).value triangleEdge01 <
      (triangleFilter triangleTime0).value triangleEdge12 ∧
    (triangleFilter triangleTimeHalf).value triangleEdge01 =
      (triangleFilter triangleTimeHalf).value triangleEdge12 ∧
    (triangleFilter triangleTime1).value triangleEdge12 <
      (triangleFilter triangleTime1).value triangleEdge01 := by
  simp [triangle_edge_values, triangleTime0, triangleTimeHalf, triangleTime1]
  norm_num

/-- Every compatible enumeration reverses the two edges after the
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

/-- Every fiber of the concrete family is represented by its full face
template, including the crossing fiber with tied edge grades. -/
private theorem triangle_diagram_template (t : Set.Icc (0 : ℝ) 1) :
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

/-- Both edge orders remain compatible at the crossing time: their tied-edge
templates evaluate to the same sublevel persistence diagram. -/
theorem triangle_explicit_midpoint_diagrams :
    evaluateFaceTemplate (ZMod 2) triangleCompatibleHalf0
        (triangleFilter triangleTimeHalf) triangleCompatibleHalf0.monotone 0 =
      dgm (ZMod 2) (triangleFilter triangleTimeHalf) 0 ∧
    evaluateFaceTemplate (ZMod 2) triangleCompatibleHalf1
        (triangleFilter triangleTimeHalf) triangleCompatibleHalf1.monotone 0 =
      dgm (ZMod 2) (triangleFilter triangleTimeHalf) 0 := by
  exact ⟨evaluateFaceTemplate_eq_dgm (ZMod 2) triangleCompatibleHalf0
    (triangleFilter triangleTimeHalf) triangleCompatibleHalf0.monotone 0,
    evaluateFaceTemplate_eq_dgm (ZMod 2) triangleCompatibleHalf1
      (triangleFilter triangleTimeHalf) triangleCompatibleHalf1.monotone 0⟩

/-! The six prefix attachments used to test the changing H₀ pair labels. -/

private theorem triangle_order0_entering_faces :
    (∀ i : Fin (faceCount triangleBoundary),
      (faceStepAttachment triangleCompatible0 i).simplex =
        if i.val = 0 then ({0} : Finset (Fin 3))
        else if i.val = 1 then {2}
        else if i.val = 2 then {1}
        else if i.val = 3 then {0, 1}
        else if i.val = 4 then {1, 2}
        else {0, 2}) := by
  intro i
  fin_cases i <;>
    simp [faceStepAttachment, triangleCompatible0,
      triangleOrder0, triangleOrder0Fun,
      triangleVertex0, triangleVertex1, triangleVertex2,
      triangleEdge01, triangleEdge12, triangleEdge02]

private theorem triangle_order1_entering_faces :
    (∀ i : Fin (faceCount triangleBoundary),
      (faceStepAttachment triangleCompatible1 i).simplex =
        if i.val = 0 then ({0} : Finset (Fin 3))
        else if i.val = 1 then {2}
        else if i.val = 2 then {1}
        else if i.val = 3 then {1, 2}
        else if i.val = 4 then {0, 1}
        else {0, 2}) := by
  intro i
  fin_cases i <;>
    simp [faceStepAttachment, triangleCompatible1,
      triangleOrder1, triangleOrder1Fun,
      triangleVertex0, triangleVertex1, triangleVertex2,
      triangleEdge01, triangleEdge12, triangleEdge02]

private def triangleIndex (i : Fin 6) : Fin (faceCount triangleBoundary) :=
  Fin.cast triangleBoundary_faceCount.symm i

private theorem triangle_prefix2_of_attachments
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (v0' : (faceStepAttachment e (triangleIndex 0)).simplex = {0})
    (v2' : (faceStepAttachment e (triangleIndex 1)).simplex = {2})
    (s : Finset (Fin 3)) :
    s ∈ e.prefixComplex 2 ↔ s = {0} ∨ s = {2} := by
  have h0 := (faceStepAttachment e (triangleIndex 0)).face_iff s
  have h1 := (faceStepAttachment e (triangleIndex 1)).face_iff s
  have hz : s ∉ e.prefixComplex 0 := by
    rw [e.prefixComplex_zero]
    simp
  have h0' : s ∈ e.prefixComplex 1 ↔
      s ∈ e.prefixComplex 0 ∨ s = {0} := by
    rw [v0'] at h0
    simpa [triangleIndex] using h0
  have h1' : s ∈ e.prefixComplex 2 ↔
      s ∈ e.prefixComplex 1 ∨ s = {2} := by
    rw [v2'] at h1
    simpa [triangleIndex] using h1
  simp only [h1', h0', hz, false_or]

private theorem triangle_prefix3_of_attachments
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (v0' : (faceStepAttachment e (triangleIndex 0)).simplex = {0})
    (v2' : (faceStepAttachment e (triangleIndex 1)).simplex = {2})
    (v1' : (faceStepAttachment e (triangleIndex 2)).simplex = {1})
    (s : Finset (Fin 3)) :
    s ∈ e.prefixComplex 3 ↔ s = {0} ∨ s = {2} ∨ s = {1} := by
  have h0 := (faceStepAttachment e (triangleIndex 0)).face_iff s
  have h1 := (faceStepAttachment e (triangleIndex 1)).face_iff s
  have h2 := (faceStepAttachment e (triangleIndex 2)).face_iff s
  have hz : s ∉ e.prefixComplex 0 := by
    rw [e.prefixComplex_zero]
    simp
  have h0' : s ∈ e.prefixComplex 1 ↔
      s ∈ e.prefixComplex 0 ∨ s = {0} := by
    rw [v0'] at h0
    simpa [triangleIndex] using h0
  have h1' : s ∈ e.prefixComplex 2 ↔
      s ∈ e.prefixComplex 1 ∨ s = {2} := by
    rw [v2'] at h1
    simpa [triangleIndex] using h1
  have h2' : s ∈ e.prefixComplex 3 ↔
      s ∈ e.prefixComplex 2 ∨ s = {1} := by
    rw [v1'] at h2
    simpa [triangleIndex] using h2
  simp only [h2', h1', h0', hz, false_or, or_assoc]

private theorem triangle_order0_prefix3 (s : Finset (Fin 3)) :
    s ∈ triangleCompatible0.prefixComplex 3 ↔
      s = {0} ∨ s = {2} ∨ s = {1} := by
  have v0' : (faceStepAttachment triangleCompatible0
      (triangleIndex 0)).simplex = {0} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 0)
  have v2' : (faceStepAttachment triangleCompatible0
      (triangleIndex 1)).simplex = {2} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 1)
  have v1' : (faceStepAttachment triangleCompatible0
      (triangleIndex 2)).simplex = {1} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 2)
  exact triangle_prefix3_of_attachments triangleCompatible0 v0' v2' v1' s

private theorem triangle_order0_prefix2 (s : Finset (Fin 3)) :
    s ∈ triangleCompatible0.prefixComplex 2 ↔ s = {0} ∨ s = {2} := by
  have v0' : (faceStepAttachment triangleCompatible0
      (triangleIndex 0)).simplex = {0} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 0)
  have v2' : (faceStepAttachment triangleCompatible0
      (triangleIndex 1)).simplex = {2} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 1)
  exact triangle_prefix2_of_attachments triangleCompatible0 v0' v2' s

private theorem triangle_order0_prefix1 :
    triangleCompatible0.prefixComplex 1 = singletonFace (0 : Fin 3) := by
  ext s
  change s ∈ triangleCompatible0.prefixComplex 1 ↔
    s ∈ singletonFace (0 : Fin 3)
  have h := (faceStepAttachment triangleCompatible0 (triangleIndex 0)).face_iff s
  have v0' : (faceStepAttachment triangleCompatible0
      (triangleIndex 0)).simplex = {0} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 0)
  rw [v0'] at h
  have h' : s ∈ triangleCompatible0.prefixComplex 1 ↔
      s ∈ triangleCompatible0.prefixComplex 0 ∨ s = {0} := by
    simpa [triangleIndex] using h
  rw [h', triangleCompatible0.prefixComplex_zero]
  simp [mem_singletonFace_iff]

private theorem triangle_order1_prefix3 (s : Finset (Fin 3)) :
    s ∈ triangleCompatible1.prefixComplex 3 ↔
      s = {0} ∨ s = {2} ∨ s = {1} := by
  have v0' : (faceStepAttachment triangleCompatible1
      (triangleIndex 0)).simplex = {0} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 0)
  have v2' : (faceStepAttachment triangleCompatible1
      (triangleIndex 1)).simplex = {2} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 1)
  have v1' : (faceStepAttachment triangleCompatible1
      (triangleIndex 2)).simplex = {1} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 2)
  exact triangle_prefix3_of_attachments triangleCompatible1 v0' v2' v1' s

private theorem triangle_order1_prefix2 (s : Finset (Fin 3)) :
    s ∈ triangleCompatible1.prefixComplex 2 ↔ s = {0} ∨ s = {2} := by
  have v0' : (faceStepAttachment triangleCompatible1
      (triangleIndex 0)).simplex = {0} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 0)
  have v2' : (faceStepAttachment triangleCompatible1
      (triangleIndex 1)).simplex = {2} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 1)
  exact triangle_prefix2_of_attachments triangleCompatible1 v0' v2' s

private theorem triangle_order1_prefix1 :
    triangleCompatible1.prefixComplex 1 = singletonFace (0 : Fin 3) := by
  ext s
  change s ∈ triangleCompatible1.prefixComplex 1 ↔
    s ∈ singletonFace (0 : Fin 3)
  have h := (faceStepAttachment triangleCompatible1 (triangleIndex 0)).face_iff s
  have v0' : (faceStepAttachment triangleCompatible1
      (triangleIndex 0)).simplex = {0} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 0)
  rw [v0'] at h
  have h' : s ∈ triangleCompatible1.prefixComplex 1 ↔
      s ∈ triangleCompatible1.prefixComplex 0 ∨ s = {0} := by
    simpa [triangleIndex] using h
  rw [h', triangleCompatible1.prefixComplex_zero]
  simp [mem_singletonFace_iff]

private theorem triangle_order0_prefix4 (s : Finset (Fin 3)) :
    s ∈ triangleCompatible0.prefixComplex 4 ↔
      s = {0} ∨ s = {2} ∨ s = {1} ∨ s = {0, 1} := by
  have h := (faceStepAttachment triangleCompatible0 (triangleIndex 3)).face_iff s
  have hedge : (faceStepAttachment triangleCompatible0
      (triangleIndex 3)).simplex = {0, 1} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 3)
  rw [hedge] at h
  have h' : s ∈ triangleCompatible0.prefixComplex 4 ↔
      s ∈ triangleCompatible0.prefixComplex 3 ∨ s = {0, 1} := by
    simpa [triangleIndex] using h
  simp only [h', triangle_order0_prefix3, or_assoc]

private theorem triangle_order1_prefix4 (s : Finset (Fin 3)) :
    s ∈ triangleCompatible1.prefixComplex 4 ↔
      s = {0} ∨ s = {2} ∨ s = {1} ∨ s = {1, 2} := by
  have h := (faceStepAttachment triangleCompatible1 (triangleIndex 3)).face_iff s
  have hedge : (faceStepAttachment triangleCompatible1
      (triangleIndex 3)).simplex = {1, 2} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 3)
  rw [hedge] at h
  have h' : s ∈ triangleCompatible1.prefixComplex 4 ↔
      s ∈ triangleCompatible1.prefixComplex 3 ∨ s = {1, 2} := by
    simpa [triangleIndex] using h
  simp only [h', triangle_order1_prefix3, or_assoc]

private theorem triangle_order0_prefix5 (s : Finset (Fin 3)) :
    s ∈ triangleCompatible0.prefixComplex 5 ↔
      s = {0} ∨ s = {2} ∨ s = {1} ∨ s = {0, 1} ∨ s = {1, 2} := by
  have h := (faceStepAttachment triangleCompatible0 (triangleIndex 4)).face_iff s
  have hedge : (faceStepAttachment triangleCompatible0
      (triangleIndex 4)).simplex = {1, 2} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 4)
  rw [hedge] at h
  have h' : s ∈ triangleCompatible0.prefixComplex 5 ↔
      s ∈ triangleCompatible0.prefixComplex 4 ∨ s = {1, 2} := by
    simpa [triangleIndex] using h
  simp only [h', triangle_order0_prefix4, or_assoc]

private theorem triangle_order1_prefix5 (s : Finset (Fin 3)) :
    s ∈ triangleCompatible1.prefixComplex 5 ↔
      s = {0} ∨ s = {2} ∨ s = {1} ∨ s = {1, 2} ∨ s = {0, 1} := by
  have h := (faceStepAttachment triangleCompatible1 (triangleIndex 4)).face_iff s
  have hedge : (faceStepAttachment triangleCompatible1
      (triangleIndex 4)).simplex = {0, 1} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 4)
  rw [hedge] at h
  have h' : s ∈ triangleCompatible1.prefixComplex 5 ↔
      s ∈ triangleCompatible1.prefixComplex 4 ∨ s = {0, 1} := by
    simpa [triangleIndex] using h
  simp only [h', triangle_order1_prefix4, or_assoc]

private theorem triangle_prefix2_eq :
    triangleCompatible0.prefixComplex 2 =
      triangleCompatible1.prefixComplex 2 := by
  ext s
  change s ∈ triangleCompatible0.prefixComplex 2 ↔
    s ∈ triangleCompatible1.prefixComplex 2
  simp only [triangle_order0_prefix2, triangle_order1_prefix2]

private theorem triangle_prefix3_eq :
    triangleCompatible0.prefixComplex 3 =
      triangleCompatible1.prefixComplex 3 := by
  ext s
  change s ∈ triangleCompatible0.prefixComplex 3 ↔
    s ∈ triangleCompatible1.prefixComplex 3
  simp only [triangle_order0_prefix3, triangle_order1_prefix3]

private theorem triangle_prefix5_eq :
    triangleCompatible0.prefixComplex 5 =
      triangleCompatible1.prefixComplex 5 := by
  ext s
  change s ∈ triangleCompatible0.prefixComplex 5 ↔
    s ∈ triangleCompatible1.prefixComplex 5
  rw [triangle_order0_prefix5, triangle_order1_prefix5]
  tauto

private theorem triangle_order0_prefix4_only_edge
    (σ : Face (triangleCompatible0.prefixComplex 4) 1) :
    σ.1 = {0, 1} := by
  rcases (triangle_order0_prefix4 σ.1).mp σ.2.1 with h | h | h | h
  · have hc := σ.2.2
    simp [h] at hc
  · have hc := σ.2.2
    simp [h] at hc
  · have hc := σ.2.2
    simp [h] at hc
  · exact h

private theorem triangle_order1_prefix4_only_edge
    (σ : Face (triangleCompatible1.prefixComplex 4) 1) :
    σ.1 = {1, 2} := by
  rcases (triangle_order1_prefix4 σ.1).mp σ.2.1 with h | h | h | h
  · have hc := σ.2.2
    simp [h] at hc
  · have hc := σ.2.2
    simp [h] at hc
  · have hc := σ.2.2
    simp [h] at hc
  · exact h

private instance triangle_prefix2_no_edges :
    IsEmpty (Face (triangleCompatible0.prefixComplex 2) 1) :=
  ⟨fun σ => by
    have hs := (triangle_order0_prefix2 σ.1).mp σ.2.1
    have hc := σ.2.2
    rcases hs with h | h <;> simp [h] at hc⟩

private instance triangle_prefix1_no_edges :
    IsEmpty (Face (triangleCompatible0.prefixComplex 1) 1) := by
  rw [triangle_order0_prefix1]
  infer_instance

private noncomputable instance triangle_prefix1_vertices_fintype :
    Fintype (Face (triangleCompatible0.prefixComplex 1) 0) :=
  Fintype.ofFinite _

set_option linter.style.haveILetI false in
private theorem triangle_prefix1_h0_dim :
    Module.finrank (ZMod 2)
      (simplicialHomology (triangleCompatible0.prefixComplex 1) (ZMod 2) 0) = 1 := by
  rw [finrank_zeroHomology_of_no_edges]
  have hsub : Subsingleton (Face (triangleCompatible0.prefixComplex 1) 0) := by
    rw [triangle_order0_prefix1]
    infer_instance
  have hnonempty : Nonempty (Face (triangleCompatible0.prefixComplex 1) 0) := by
    refine ⟨⟨{0}, ?_, by decide⟩⟩
    rw [triangle_order0_prefix1]
    exact (mem_singletonFace_iff (0 : Fin 3) {0}).mpr rfl
  haveI : Unique (Face (triangleCompatible0.prefixComplex 1) 0) :=
    ⟨⟨Classical.choice hnonempty⟩, by intro a; exact Subsingleton.elim _ _⟩
  exact Fintype.card_unique

private instance triangle_prefix3_no_edges :
    IsEmpty (Face (triangleCompatible0.prefixComplex 3) 1) :=
  ⟨fun σ => by
    have hs := (triangle_order0_prefix3 σ.1).mp σ.2.1
    have hc := σ.2.2
    rcases hs with h | h | h <;> simp [h] at hc⟩

private def triangle_prefix2_vertex (i : Fin 2) :
    Face (triangleCompatible0.prefixComplex 2) 0 :=
  ⟨if i = 0 then {0} else {2},
    by apply (triangle_order0_prefix2 _).mpr; fin_cases i <;> simp,
    by fin_cases i <;> decide⟩

private def triangle_prefix3_vertex (i : Fin 3) :
    Face (triangleCompatible0.prefixComplex 3) 0 :=
  ⟨if i = 0 then {0} else if i = 1 then {2} else {1},
    by apply (triangle_order0_prefix3 _).mpr; fin_cases i <;> simp,
    by fin_cases i <;> decide⟩

private theorem triangle_prefix2_vertex_bijective :
    Function.Bijective triangle_prefix2_vertex := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;>
      first | rfl | (simp [triangle_prefix2_vertex] at hv)
  · intro σ
    rcases (triangle_order0_prefix2 σ.1).mp σ.2.1 with h | h
    · exact ⟨0, Subtype.ext (by simpa [triangle_prefix2_vertex] using h.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [triangle_prefix2_vertex] using h.symm)⟩

private theorem triangle_prefix3_vertex_bijective :
    Function.Bijective triangle_prefix3_vertex := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;>
      first | rfl | (simp [triangle_prefix3_vertex] at hv)
  · intro σ
    rcases (triangle_order0_prefix3 σ.1).mp σ.2.1 with h | h | h
    · exact ⟨0, Subtype.ext (by simpa [triangle_prefix3_vertex] using h.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [triangle_prefix3_vertex] using h.symm)⟩
    · exact ⟨2, Subtype.ext (by simpa [triangle_prefix3_vertex] using h.symm)⟩

private noncomputable instance triangle_prefix2_vertex_fintype :
    Fintype (Face (triangleCompatible0.prefixComplex 2) 0) :=
  Fintype.ofEquiv (Fin 2)
    (Equiv.ofBijective triangle_prefix2_vertex triangle_prefix2_vertex_bijective)

private noncomputable instance triangle_prefix3_vertex_fintype :
    Fintype (Face (triangleCompatible0.prefixComplex 3) 0) :=
  Fintype.ofEquiv (Fin 3)
    (Equiv.ofBijective triangle_prefix3_vertex triangle_prefix3_vertex_bijective)

private theorem triangle_prefix2_vertex_card :
    Fintype.card (Face (triangleCompatible0.prefixComplex 2) 0) = 2 := by
  exact Fintype.card_congr
    (Equiv.ofBijective triangle_prefix2_vertex triangle_prefix2_vertex_bijective).symm

private theorem triangle_prefix3_vertex_card :
    Fintype.card (Face (triangleCompatible0.prefixComplex 3) 0) = 3 := by
  exact Fintype.card_congr
    (Equiv.ofBijective triangle_prefix3_vertex triangle_prefix3_vertex_bijective).symm

private theorem triangle_prefix2_h0_dim :
    Module.finrank (ZMod 2)
      (simplicialHomology (triangleCompatible0.prefixComplex 2) (ZMod 2) 0) = 2 := by
  rw [finrank_zeroHomology_of_no_edges, triangle_prefix2_vertex_card]

private theorem triangle_prefix2_chain_decompose
    (c : Chain (triangleCompatible0.prefixComplex 2) (ZMod 2) 0) :
    c = Finsupp.single (triangle_prefix2_vertex 0)
          (c (triangle_prefix2_vertex 0)) +
        Finsupp.single (triangle_prefix2_vertex 1)
          (c (triangle_prefix2_vertex 1)) := by
  apply Finsupp.ext
  intro σ
  obtain ⟨i, rfl⟩ := triangle_prefix2_vertex_bijective.2 σ
  fin_cases i <;> simp [triangle_prefix2_vertex]

private def triangle_order1_prefix2_vertex (i : Fin 2) :
    Face (triangleCompatible1.prefixComplex 2) 0 :=
  ⟨if i = 0 then {0} else {2},
    by apply (triangle_order1_prefix2 _).mpr; fin_cases i <;> simp,
    by fin_cases i <;> decide⟩

private theorem triangle_order1_prefix2_vertex_bijective :
    Function.Bijective triangle_order1_prefix2_vertex := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;>
      first | rfl | (simp [triangle_order1_prefix2_vertex] at hv)
  · intro σ
    rcases (triangle_order1_prefix2 σ.1).mp σ.2.1 with h | h
    · exact ⟨0, Subtype.ext (by simpa [triangle_order1_prefix2_vertex] using h.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [triangle_order1_prefix2_vertex] using h.symm)⟩

private theorem triangle_order1_prefix2_chain_decompose
    (c : Chain (triangleCompatible1.prefixComplex 2) (ZMod 2) 0) :
    c = Finsupp.single (triangle_order1_prefix2_vertex 0)
          (c (triangle_order1_prefix2_vertex 0)) +
        Finsupp.single (triangle_order1_prefix2_vertex 1)
          (c (triangle_order1_prefix2_vertex 1)) := by
  apply Finsupp.ext
  intro σ
  obtain ⟨i, rfl⟩ := triangle_order1_prefix2_vertex_bijective.2 σ
  fin_cases i <;> simp [triangle_order1_prefix2_vertex]

private theorem triangle_order0_component_constant (σ :
    Face (triangleCompatible0.prefixComplex 4) 1) :
    (2 : Fin 3) ∉ (deletedFace _ 0 σ 0).1 ↔
      (2 : Fin 3) ∉ (deletedFace _ 0 σ 1).1 := by
  have hedge := triangle_order0_prefix4_only_edge σ
  have hnot : (2 : Fin 3) ∉ σ.1 := by rw [hedge]; decide
  have h0 : (deletedFace _ 0 σ 0).1 ⊆ σ.1 :=
    Finset.erase_subset _ _
  have h1 : (deletedFace _ 0 σ 1).1 ⊆ σ.1 :=
    Finset.erase_subset _ _
  exact iff_of_true (fun hm => hnot (h0 hm))
    (fun hm => hnot (h1 hm))

private theorem triangle_order1_component_constant (σ :
    Face (triangleCompatible1.prefixComplex 4) 1) :
    (0 : Fin 3) ∈ (deletedFace _ 0 σ 0).1 ↔
      (0 : Fin 3) ∈ (deletedFace _ 0 σ 1).1 := by
  have hedge := triangle_order1_prefix4_only_edge σ
  have hnot : (0 : Fin 3) ∉ σ.1 := by rw [hedge]; decide
  have h0 : (deletedFace _ 0 σ 0).1 ⊆ σ.1 :=
    Finset.erase_subset _ _
  have h1 : (deletedFace _ 0 σ 1).1 ⊆ σ.1 :=
    Finset.erase_subset _ _
  exact iff_of_false (fun hm => hnot (h0 hm))
    (fun hm => hnot (h1 hm))

private theorem triangle_prefix3_h0_dim :
    Module.finrank (ZMod 2)
      (simplicialHomology (triangleCompatible0.prefixComplex 3) (ZMod 2) 0) = 3 := by
  rw [finrank_zeroHomology_of_no_edges, triangle_prefix3_vertex_card]

private def triangleStage (i : Fin 7) :
    Fin (faceCount triangleBoundary + 1) :=
  Fin.cast (by rw [triangleBoundary_faceCount]) i

private theorem triangle_rank33
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (he : e.prefixComplex 3 = triangleCompatible0.prefixComplex 3) :
    structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 3) (triangleStage 3) (by decide) = 3 := by
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  change Module.finrank (ZMod 2)
    (simplicialHomology (e.prefixComplex 3) (ZMod 2) 0) = 3
  rw [he]
  exact triangle_prefix3_h0_dim

private theorem triangle_rank23
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (he2 : e.prefixComplex 2 = triangleCompatible0.prefixComplex 2)
    (hface : (faceStepAttachment e (triangleIndex 2)).simplex = {1}) :
    structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 2) (triangleStage 3) (by decide) = 2 := by
  have hq : (e.enum (triangleIndex 2)).val.card - 1 = 0 := by
    change (faceStepAttachment e (triangleIndex 2)).simplex.card - 1 = 0
    rw [hface]
    decide
  let A : SimplexAttachment (e.prefixComplex 2) (e.prefixComplex 3) 0 := by
    have hA := faceStepAttachment e (triangleIndex 2)
    rw [hq] at hA
    simpa [triangleIndex] using hA
  have hinj := A.homologyIncl_injective_of_succ_ne (ZMod 2) (by decide : 0 + 1 ≠ 0)
  change Module.finrank (ZMod 2)
    (LinearMap.range (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom) = 2
  rw [LinearMap.finrank_range_of_inj hinj, he2]
  exact triangle_prefix2_h0_dim

set_option linter.style.haveILetI false in
private theorem triangle_rank34
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (he3 : e.prefixComplex 3 = triangleCompatible0.prefixComplex 3)
    (hface : (faceStepAttachment e (triangleIndex 3)).simplex.card = 2) :
    structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 3) (triangleStage 4) (by decide) = 2 := by
  have hq : (e.enum (triangleIndex 3)).val.card - 1 = 1 := by
    change (faceStepAttachment e (triangleIndex 3)).simplex.card - 1 = 1
    omega
  let A : SimplexAttachment (e.prefixComplex 3) (e.prefixComplex 4) 1 := by
    have hA := faceStepAttachment e (triangleIndex 3)
    rw [hq] at hA
    simpa [triangleIndex] using hA
  haveI : IsEmpty (Face (e.prefixComplex 3) 1) := by
    rw [he3]
    infer_instance
  have hdeath := A.positive_death (ZMod 2)
    (A.attachingClass_ne_zero_of_no_old_coface (ZMod 2))
  have hdim : Module.finrank (ZMod 2)
      (simplicialHomology (e.prefixComplex 3) (ZMod 2) 0) = 3 := by
    rw [he3]
    exact triangle_prefix3_h0_dim
  have hr := LinearMap.finrank_range_add_finrank_ker
    (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom
  change Module.finrank (ZMod 2)
      (LinearMap.range (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom) +
      Module.finrank (ZMod 2)
        (LinearMap.ker (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom) =
        Module.finrank (ZMod 2)
          (simplicialHomology (e.prefixComplex 3) (ZMod 2) 0) at hr
  rw [hdeath.2.2.1, hdim] at hr
  change Module.finrank (ZMod 2)
      (LinearMap.range (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom) = 2
  omega

set_option linter.style.haveILetI false in
private theorem triangle_stage4_h0_dim
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (he3 : e.prefixComplex 3 = triangleCompatible0.prefixComplex 3)
    (hface : (faceStepAttachment e (triangleIndex 3)).simplex.card = 2) :
    Module.finrank (ZMod 2)
      (simplicialHomology (e.prefixComplex 4) (ZMod 2) 0) = 2 := by
  have hq : (e.enum (triangleIndex 3)).val.card - 1 = 1 := by
    change (faceStepAttachment e (triangleIndex 3)).simplex.card - 1 = 1
    omega
  let A : SimplexAttachment (e.prefixComplex 3) (e.prefixComplex 4) 1 := by
    have hA := faceStepAttachment e (triangleIndex 3)
    rw [hq] at hA
    simpa [triangleIndex] using hA
  haveI : IsEmpty (Face (e.prefixComplex 3) 1) := by
    rw [he3]
    infer_instance
  have hsurj := (A.positive_death (ZMod 2)
    (A.attachingClass_ne_zero_of_no_old_coface (ZMod 2))).1
  have hr := triangle_rank34 e he3 hface
  change Module.finrank (ZMod 2)
    (LinearMap.range (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom) = 2 at hr
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
  exact hr

private theorem triangle_order0_rank24 :
    structureMapRank (facePrefixModule (ZMod 2) triangleCompatible0 0)
      (triangleStage 2) (triangleStage 4) (by decide) = 2 := by
  let h := triangleCompatible0.prefixComplex_mono (by decide : 2 ≤ 4)
  have hinj : Function.Injective (simplicialQuotientIncl (ZMod 2) h 0) :=
    quotientIncl_injective_of_two_vertices_separated
      (triangleCompatible0.prefixComplex 2) (ZMod 2) h
      (triangle_prefix2_vertex 0) (triangle_prefix2_vertex 1)
      triangle_prefix2_chain_decompose
      (fun σ => (2 : Fin 3) ∉ σ.1)
      triangle_order0_component_constant
      (by decide) (by decide)
  change Module.finrank (ZMod 2)
    (LinearMap.range (simplicialHomologyIncl (ZMod 2) h 0).hom) = 2
  rw [finrank_homologyIncl_range_eq_quotientIncl_range,
    LinearMap.finrank_range_of_inj hinj]
  exact ((homologyKernelQuotient (ZMod 2)
    (simplicialChainComplex (triangleCompatible0.prefixComplex 2) (ZMod 2)) 0
      ).toLinearEquiv.finrank_eq).symm.trans triangle_prefix2_h0_dim

private theorem triangle_order1_rank24 :
    structureMapRank (facePrefixModule (ZMod 2) triangleCompatible1 0)
      (triangleStage 2) (triangleStage 4) (by decide) = 2 := by
  let h := triangleCompatible1.prefixComplex_mono (by decide : 2 ≤ 4)
  have hinj : Function.Injective (simplicialQuotientIncl (ZMod 2) h 0) :=
    quotientIncl_injective_of_two_vertices_separated
      (triangleCompatible1.prefixComplex 2) (ZMod 2) h
      (triangle_order1_prefix2_vertex 0) (triangle_order1_prefix2_vertex 1)
      triangle_order1_prefix2_chain_decompose
      (fun σ => (0 : Fin 3) ∈ σ.1)
      triangle_order1_component_constant
      (by decide) (by decide)
  change Module.finrank (ZMod 2)
    (LinearMap.range (simplicialHomologyIncl (ZMod 2) h 0).hom) = 2
  rw [finrank_homologyIncl_range_eq_quotientIncl_range,
    LinearMap.finrank_range_of_inj hinj]
  exact ((homologyKernelQuotient (ZMod 2)
    (simplicialChainComplex (triangleCompatible1.prefixComplex 2) (ZMod 2)) 0
      ).toLinearEquiv.finrank_eq).symm.trans (by
    rw [← triangle_prefix2_eq]
    exact triangle_prefix2_h0_dim)

private theorem triangle_order0_second_edge_death :
    Function.Surjective (simplicialHomologyIncl (ZMod 2)
      (triangleCompatible0.prefixComplex_mono (by decide : 4 ≤ 5)) 0).hom ∧
    Module.finrank (ZMod 2)
      (LinearMap.ker (simplicialHomologyIncl (ZMod 2)
        (triangleCompatible0.prefixComplex_mono (by decide : 4 ≤ 5)) 0).hom) = 1 := by
  have hface : (faceStepAttachment triangleCompatible0 (triangleIndex 4)).simplex =
      {1, 2} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 4)
  have hq : (triangleCompatible0.enum (triangleIndex 4)).val.card - 1 = 1 := by
    change (faceStepAttachment triangleCompatible0 (triangleIndex 4)).simplex.card - 1 = 1
    rw [hface]
    decide
  let A : SimplexAttachment (triangleCompatible0.prefixComplex 4)
      (triangleCompatible0.prefixComplex 5) 1 := by
    have hA := faceStepAttachment triangleCompatible0 (triangleIndex 4)
    rw [hq] at hA
    simpa [triangleIndex] using hA
  have hnew : A.simplex = {1, 2} := hface
  have horder : A.simplex.orderEmbOfFin A.card_simplex =
      Fin.succAboveOrderEmb (0 : Fin 3) := by
    have hs : A.simplex = ({(0 : Fin 3)}ᶜ : Finset (Fin 3)) := by
      rw [hnew]
      decide
    simp [hs]
  have h0 : (2 : Fin 3) ∈ (A.oldDeletedFace 0).1 := by
    change (2 : Fin 3) ∈
      A.simplex.erase (A.simplex.orderEmbOfFin A.card_simplex 0)
    rw [horder, hnew]
    decide
  have h1 : (2 : Fin 3) ∉ (A.oldDeletedFace 1).1 := by
    change (2 : Fin 3) ∉
      A.simplex.erase (A.simplex.orderEmbOfFin A.card_simplex 1)
    rw [horder, hnew]
    decide
  have hdeath := A.positive_death (ZMod 2)
    (SimplexAttachment.attachingHomologyClass_ne_zero_of_separated_vertices
      (triangleCompatible0.prefixComplex 4) (ZMod 2) A
      (fun σ => (2 : Fin 3) ∈ σ.1)
      (by
        intro σ
        have hedge := triangle_order0_prefix4_only_edge σ
        have hnot : (2 : Fin 3) ∉ σ.1 := by rw [hedge]; decide
        have hdel0 : (deletedFace _ 0 σ 0).1 ⊆ σ.1 := Finset.erase_subset _ _
        have hdel1 : (deletedFace _ 0 σ 1).1 ⊆ σ.1 := Finset.erase_subset _ _
        exact iff_of_false (fun hm => hnot (hdel0 hm))
          (fun hm => hnot (hdel1 hm)))
      h0 h1)
  simpa only [SimplexAttachment.inclusion] using
    (show Function.Surjective (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom ∧
      Module.finrank (ZMod 2)
        (LinearMap.ker (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom) = 1
      from ⟨hdeath.1, hdeath.2.2.1⟩)

private theorem triangle_order1_second_edge_death :
    Function.Surjective (simplicialHomologyIncl (ZMod 2)
      (triangleCompatible1.prefixComplex_mono (by decide : 4 ≤ 5)) 0).hom ∧
    Module.finrank (ZMod 2)
      (LinearMap.ker (simplicialHomologyIncl (ZMod 2)
        (triangleCompatible1.prefixComplex_mono (by decide : 4 ≤ 5)) 0).hom) = 1 := by
  have hface : (faceStepAttachment triangleCompatible1 (triangleIndex 4)).simplex =
      {0, 1} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 4)
  have hq : (triangleCompatible1.enum (triangleIndex 4)).val.card - 1 = 1 := by
    change (faceStepAttachment triangleCompatible1 (triangleIndex 4)).simplex.card - 1 = 1
    rw [hface]
    decide
  let A : SimplexAttachment (triangleCompatible1.prefixComplex 4)
      (triangleCompatible1.prefixComplex 5) 1 := by
    have hA := faceStepAttachment triangleCompatible1 (triangleIndex 4)
    rw [hq] at hA
    simpa [triangleIndex] using hA
  have hnew : A.simplex = {0, 1} := hface
  have horder : A.simplex.orderEmbOfFin A.card_simplex =
      Fin.succAboveOrderEmb (2 : Fin 3) := by
    have hs : A.simplex = ({(2 : Fin 3)}ᶜ : Finset (Fin 3)) := by
      rw [hnew]
      decide
    simp [hs]
  have h0 : (0 : Fin 3) ∉ (A.oldDeletedFace 0).1 := by
    change (0 : Fin 3) ∉
      A.simplex.erase (A.simplex.orderEmbOfFin A.card_simplex 0)
    rw [horder, hnew]
    decide
  have h1 : ¬ (0 : Fin 3) ∉ (A.oldDeletedFace 1).1 := by
    change ¬ (0 : Fin 3) ∉
      A.simplex.erase (A.simplex.orderEmbOfFin A.card_simplex 1)
    rw [horder, hnew]
    decide
  have hdeath := A.positive_death (ZMod 2)
    (SimplexAttachment.attachingHomologyClass_ne_zero_of_separated_vertices
      (triangleCompatible1.prefixComplex 4) (ZMod 2) A
      (fun σ => (0 : Fin 3) ∉ σ.1)
      (by intro σ; exact not_congr (triangle_order1_component_constant σ))
      h0 h1)
  simpa only [SimplexAttachment.inclusion] using
    (show Function.Surjective (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom ∧
      Module.finrank (ZMod 2)
        (LinearMap.ker (simplicialHomologyIncl (ZMod 2) A.inclusion 0).hom) = 1
      from ⟨hdeath.1, hdeath.2.2.1⟩)

private theorem triangle_stage5_h0_dim
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (h4 : Module.finrank (ZMod 2)
      (simplicialHomology (e.prefixComplex 4) (ZMod 2) 0) = 2)
    (hdeath : Function.Surjective (simplicialHomologyIncl (ZMod 2)
        (e.prefixComplex_mono (by decide : 4 ≤ 5)) 0).hom ∧
      Module.finrank (ZMod 2)
        (LinearMap.ker (simplicialHomologyIncl (ZMod 2)
          (e.prefixComplex_mono (by decide : 4 ≤ 5)) 0).hom) = 1) :
    Module.finrank (ZMod 2)
      (simplicialHomology (e.prefixComplex 5) (ZMod 2) 0) = 1 := by
  have hr := LinearMap.finrank_range_add_finrank_ker
    (simplicialHomologyIncl (ZMod 2)
      (e.prefixComplex_mono (by decide : 4 ≤ 5)) 0).hom
  rw [LinearMap.range_eq_top.mpr hdeath.1, finrank_top, hdeath.2, h4] at hr
  omega

private theorem triangle_order0_first_edge_card :
    (faceStepAttachment triangleCompatible0 (triangleIndex 3)).simplex.card = 2 := by
  have h := triangle_order0_entering_faces (triangleIndex 3)
  simpa [triangleIndex] using congrArg Finset.card h

private theorem triangle_order1_first_edge_card :
    (faceStepAttachment triangleCompatible1 (triangleIndex 3)).simplex.card = 2 := by
  have h := triangle_order1_entering_faces (triangleIndex 3)
  simpa [triangleIndex] using congrArg Finset.card h

private theorem triangle_order0_stage5_h0_dim :
    Module.finrank (ZMod 2)
      (simplicialHomology (triangleCompatible0.prefixComplex 5) (ZMod 2) 0) = 1 :=
  triangle_stage5_h0_dim triangleCompatible0
    (triangle_stage4_h0_dim triangleCompatible0 rfl triangle_order0_first_edge_card)
    triangle_order0_second_edge_death

private theorem triangle_order1_stage5_h0_dim :
    Module.finrank (ZMod 2)
      (simplicialHomology (triangleCompatible1.prefixComplex 5) (ZMod 2) 0) = 1 :=
  triangle_stage5_h0_dim triangleCompatible1
    (triangle_stage4_h0_dim triangleCompatible1 triangle_prefix3_eq.symm
      triangle_order1_first_edge_card)
    triangle_order1_second_edge_death

private theorem triangle_rank_one_of_vertex
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (i j : Fin 7) (hij : i ≤ j) (σ : Face (e.prefixComplex i.val) 0)
    (hdim : Module.finrank (ZMod 2)
        (simplicialHomology (e.prefixComplex i.val) (ZMod 2) 0) = 1 ∨
      Module.finrank (ZMod 2)
        (simplicialHomology (e.prefixComplex j.val) (ZMod 2) 0) = 1) :
    structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage i) (triangleStage j)
      (by simpa [triangleStage] using hij) = 1 := by
  let h := e.prefixComplex_mono (Fin.le_def.mp hij)
  have hpos : 0 < Module.finrank (ZMod 2)
      (LinearMap.range (simplicialHomologyIncl (ZMod 2) h 0).hom) :=
    finrank_homologyIncl_range_pos_of_vertex
      (e.prefixComplex i.val) (ZMod 2) h σ
  have hle : Module.finrank (ZMod 2)
      (LinearMap.range (simplicialHomologyIncl (ZMod 2) h 0).hom) ≤ 1 := by
    rcases hdim with hs | ht
    · exact (LinearMap.finrank_range_le _).trans_eq hs
    · exact (LinearMap.range (simplicialHomologyIncl (ZMod 2) h 0).hom
        ).finrank_le.trans_eq ht
  change Module.finrank (ZMod 2)
    (LinearMap.range (simplicialHomologyIncl (ZMod 2) h 0).hom) = 1
  omega

private def triangle_order0_prefix1_vertex :
    Face (triangleCompatible0.prefixComplex 1) 0 :=
  ⟨{0}, by
    rw [triangle_order0_prefix1]
    exact (mem_singletonFace_iff (0 : Fin 3) {0}).mpr rfl,
    by decide⟩

private def triangle_order1_prefix1_vertex :
    Face (triangleCompatible1.prefixComplex 1) 0 :=
  ⟨{0}, by
    rw [triangle_order1_prefix1]
    exact (mem_singletonFace_iff (0 : Fin 3) {0}).mpr rfl,
    by decide⟩

private theorem triangle_multiplicities_from_ranks
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (r33 : structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 3) (triangleStage 3) (by decide) = 3)
    (r23 : structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 2) (triangleStage 3) (by decide) = 2)
    (r34 : structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 3) (triangleStage 4) (by decide) = 2)
    (r24 : structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 2) (triangleStage 4) (by decide) = 2)
    (r14 : structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 1) (triangleStage 4) (by decide) = 1)
    (r25 : structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 2) (triangleStage 5) (by decide) = 1)
    (r15 : structureMapRank (facePrefixModule (ZMod 2) e 0)
      (triangleStage 1) (triangleStage 5) (by decide) = 1) :
    barcodeMultiplicity (facePrefixBarcode (ZMod 2) e 0) 3 4 = 1 ∧
    barcodeMultiplicity (facePrefixBarcode (ZMod 2) e 0) 2 5 = 1 := by
  let M := facePrefixModule (ZMod 2) e 0
  have rankInt (i j : Fin 7) (hij : i ≤ j) :
      moduleRankInteger M i.val j.val =
        (structureMapRank M (triangleStage i) (triangleStage j)
          (by simpa [triangleStage] using hij) : ℤ) := by
    simpa only [triangleStage, Fin.val_cast] using
      (moduleRankInteger_fin M (triangleStage i) (triangleStage j)
        (by simpa [triangleStage] using hij))
  have a33 : moduleRankInteger M 3 3 = 3 := by
    simpa [M, r33] using rankInt 3 3 (by decide)
  have a23 : moduleRankInteger M 2 3 = 2 := by
    simpa [M, r23] using rankInt 2 3 (by decide)
  have a34 : moduleRankInteger M 3 4 = 2 := by
    simpa [M, r34] using rankInt 3 4 (by decide)
  have a24 : moduleRankInteger M 2 4 = 2 := by
    simpa [M, r24] using rankInt 2 4 (by decide)
  have a14 : moduleRankInteger M 1 4 = 1 := by
    simpa [M, r14] using rankInt 1 4 (by decide)
  have a25 : moduleRankInteger M 2 5 = 1 := by
    simpa [M, r25] using rankInt 2 5 (by decide)
  have a15 : moduleRankInteger M 1 5 = 1 := by
    simpa [M, r15] using rankInt 1 5 (by decide)
  have mu34 : moduleMultiplicityInteger M 3 4 = 1 := by
    change moduleRankInteger M 3 3 - moduleRankInteger M 2 3 -
      moduleRankInteger M 3 4 + moduleRankInteger M 2 4 = 1
    omega
  have mu25 : moduleMultiplicityInteger M 2 5 = 1 := by
    change moduleRankInteger M 2 4 - moduleRankInteger M 1 4 -
      moduleRankInteger M 2 5 + moduleRankInteger M 1 5 = 1
    omega
  constructor
  · have h := barcodeMultiplicity_rankBarcode M 3 4 (by decide) (by
      rw [triangleBoundary_faceCount]; decide)
    change (barcodeMultiplicity (facePrefixBarcode (ZMod 2) e 0) 3 4 : ℤ) =
      moduleMultiplicityInteger M 3 4 at h
    exact_mod_cast h.trans mu34
  · have h := barcodeMultiplicity_rankBarcode M 2 5 (by decide) (by
      rw [triangleBoundary_faceCount]; decide)
    change (barcodeMultiplicity (facePrefixBarcode (ZMod 2) e 0) 2 5 : ℤ) =
      moduleMultiplicityInteger M 2 5 at h
    exact_mod_cast h.trans mu25

/-- The prefix H₀ classes change their death attachments when the first
two edge grades exchange order. Both multiplicities use ordinary homology of
the six-face triangle boundary, not a stipulated rank diagram. -/
theorem triangle_pairing_change :
    barcodeMultiplicity (facePrefixBarcode (ZMod 2) triangleCompatible0 0) 3 4 = 1 ∧
    barcodeMultiplicity (facePrefixBarcode (ZMod 2) triangleCompatible0 0) 2 5 = 1 ∧
    barcodeMultiplicity (facePrefixBarcode (ZMod 2) triangleCompatible1 0) 3 4 = 1 ∧
    barcodeMultiplicity (facePrefixBarcode (ZMod 2) triangleCompatible1 0) 2 5 = 1 := by
  have hvertex0 : (faceStepAttachment triangleCompatible0 (triangleIndex 2)).simplex =
      {1} := by
    simpa [triangleIndex] using triangle_order0_entering_faces (triangleIndex 2)
  have hvertex1 : (faceStepAttachment triangleCompatible1 (triangleIndex 2)).simplex =
      {1} := by
    simpa [triangleIndex] using triangle_order1_entering_faces (triangleIndex 2)
  have hfirst1 : Module.finrank (ZMod 2)
      (simplicialHomology (triangleCompatible1.prefixComplex 1) (ZMod 2) 0) = 1 := by
    rw [triangle_order1_prefix1, ← triangle_order0_prefix1]
    exact triangle_prefix1_h0_dim
  have h0 := triangle_multiplicities_from_ranks triangleCompatible0
    (triangle_rank33 triangleCompatible0 rfl)
    (triangle_rank23 triangleCompatible0 rfl hvertex0)
    (triangle_rank34 triangleCompatible0 rfl triangle_order0_first_edge_card)
    triangle_order0_rank24
    (triangle_rank_one_of_vertex triangleCompatible0 1 4 (by decide)
      triangle_order0_prefix1_vertex (Or.inl triangle_prefix1_h0_dim))
    (triangle_rank_one_of_vertex triangleCompatible0 2 5 (by decide)
      (triangle_prefix2_vertex 0) (Or.inr triangle_order0_stage5_h0_dim))
    (triangle_rank_one_of_vertex triangleCompatible0 1 5 (by decide)
      triangle_order0_prefix1_vertex (Or.inr triangle_order0_stage5_h0_dim))
  have h1 := triangle_multiplicities_from_ranks triangleCompatible1
    (triangle_rank33 triangleCompatible1 triangle_prefix3_eq.symm)
    (triangle_rank23 triangleCompatible1 triangle_prefix2_eq.symm hvertex1)
    (triangle_rank34 triangleCompatible1 triangle_prefix3_eq.symm
      triangle_order1_first_edge_card)
    triangle_order1_rank24
    (triangle_rank_one_of_vertex triangleCompatible1 1 4 (by decide)
      triangle_order1_prefix1_vertex (Or.inl hfirst1))
    (triangle_rank_one_of_vertex triangleCompatible1 2 5 (by decide)
      (triangle_order1_prefix2_vertex 0) (Or.inr triangle_order1_stage5_h0_dim))
    (triangle_rank_one_of_vertex triangleCompatible1 1 5 (by decide)
      triangle_order1_prefix1_vertex (Or.inr triangle_order1_stage5_h0_dim))
  exact ⟨h0.1, h0.2, h1.1, h1.2⟩

private theorem triangle_pair34_mem
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (hpos : 0 < barcodeMultiplicity (facePrefixBarcode (ZMod 2) e 0) 3 4) :
    (triangleIndex 2, triangleIndex 3) ∈ faceTemplatePairs (ZMod 2) e 0 := by
  obtain ⟨p, hp, hb, hd⟩ :=
    faceTemplatePairs_mem_of_barcodeMultiplicity_pos (ZMod 2) e 0 3 4
      (by decide) (by rw [triangleBoundary_faceCount]; decide) hpos
  have h0 : p.1 = triangleIndex 2 := by
    apply Fin.ext
    simpa [triangleIndex] using hb
  have h1 : p.2 = triangleIndex 3 := by
    apply Fin.ext
    simpa [triangleIndex] using hd
  have hp' : p = (triangleIndex 2, triangleIndex 3) := Prod.ext h0 h1
  rw [hp'] at hp
  exact hp

private theorem triangle_pair25_mem
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (hpos : 0 < barcodeMultiplicity (facePrefixBarcode (ZMod 2) e 0) 2 5) :
    (triangleIndex 1, triangleIndex 4) ∈ faceTemplatePairs (ZMod 2) e 0 := by
  obtain ⟨p, hp, hb, hd⟩ :=
    faceTemplatePairs_mem_of_barcodeMultiplicity_pos (ZMod 2) e 0 2 5
      (by decide) (by rw [triangleBoundary_faceCount]; decide) hpos
  have h0 : p.1 = triangleIndex 1 := by
    apply Fin.ext
    simpa [triangleIndex] using hb
  have h1 : p.2 = triangleIndex 4 := by
    apply Fin.ext
    simpa [triangleIndex] using hd
  have hp' : p = (triangleIndex 1, triangleIndex 4) := Prod.ext h0 h1
  rw [hp'] at hp
  exact hp

/-- The concrete finite pairings use different edge faces on the two
sides of the crossing, even though the birth vertices are the same. -/
theorem triangle_face_pairings :
    (triangleVertex1, triangleEdge01) ∈
      (faceTemplatePairs (ZMod 2) triangleCompatible0 0).map
        (fun p => (triangleCompatible0.enum p.1, triangleCompatible0.enum p.2)) ∧
    (triangleVertex2, triangleEdge12) ∈
      (faceTemplatePairs (ZMod 2) triangleCompatible0 0).map
        (fun p => (triangleCompatible0.enum p.1, triangleCompatible0.enum p.2)) ∧
    (triangleVertex1, triangleEdge12) ∈
      (faceTemplatePairs (ZMod 2) triangleCompatible1 0).map
        (fun p => (triangleCompatible1.enum p.1, triangleCompatible1.enum p.2)) ∧
    (triangleVertex2, triangleEdge01) ∈
      (faceTemplatePairs (ZMod 2) triangleCompatible1 0).map
        (fun p => (triangleCompatible1.enum p.1, triangleCompatible1.enum p.2)) := by
  have hm := triangle_pairing_change
  constructor
  · apply Multiset.mem_map.mpr
    refine ⟨(triangleIndex 2, triangleIndex 3),
      triangle_pair34_mem triangleCompatible0 (by omega), ?_⟩
    simp [triangleCompatible0, triangleOrder0, triangleOrder0Fun, triangleIndex]
  constructor
  · apply Multiset.mem_map.mpr
    refine ⟨(triangleIndex 1, triangleIndex 4),
      triangle_pair25_mem triangleCompatible0 (by omega), ?_⟩
    simp [triangleCompatible0, triangleOrder0, triangleOrder0Fun, triangleIndex]
  constructor
  · apply Multiset.mem_map.mpr
    refine ⟨(triangleIndex 2, triangleIndex 3),
      triangle_pair34_mem triangleCompatible1 (by omega), ?_⟩
    simp [triangleCompatible1, triangleOrder1, triangleOrder1Fun, triangleIndex]
  · apply Multiset.mem_map.mpr
    refine ⟨(triangleIndex 1, triangleIndex 4),
      triangle_pair25_mem triangleCompatible1 (by omega), ?_⟩
    simp [triangleCompatible1, triangleOrder1, triangleOrder1Fun, triangleIndex]

private theorem triangle_pair_point_in_dgm
    {f : FilterFunction triangleBoundary ℝ} (e : CompatibleOrder f)
    (g : FilterFunction triangleBoundary ℝ)
    (hg : Monotone (g.value ∘ e.enum))
    (p : Fin (faceCount triangleBoundary) × Fin (faceCount triangleBoundary))
    (hp : p ∈ faceTemplatePairs (ZMod 2) e 0)
    (hne : g.value (e.enum p.1) ≠ g.value (e.enum p.2)) :
    (g.value (e.enum p.1), (g.value (e.enum p.2) : WithTop ℝ)) ∈
      (dgm (ZMod 2) g 0).points := by
  rw [← evaluateFaceTemplate_eq_dgm (ZMod 2) e g hg 0]
  change _ ∈
    (((faceTemplatePairs (ZMod 2) e 0).map (pairValues g e)).filter
      (fun q => q.1 ≠ q.2)).map (fun q => (q.1, (q.2 : WithTop ℝ))) + _
  apply Multiset.mem_add.mpr
  left
  apply Multiset.mem_map.mpr
  refine ⟨pairValues g e p, ?_, ?_⟩
  · exact Multiset.mem_filter.mpr
      ⟨Multiset.mem_map.mpr ⟨p, hp, rfl⟩, by simpa [pairValues] using hne⟩
  · rfl

/-- Both finite H₀ intervals give positive points in the crossing
diagram, even though the two edges have equal grades there. -/
theorem triangle_midpoint_diagram_points :
    (2, ((7 / 2 : ℝ) : WithTop ℝ)) ∈
      (dgm (ZMod 2) (triangleFilter triangleTimeHalf) 0).points ∧
    (1, ((7 / 2 : ℝ) : WithTop ℝ)) ∈
      (dgm (ZMod 2) (triangleFilter triangleTimeHalf) 0).points := by
  have hm := triangle_pairing_change
  have hp34 := triangle_pair34_mem triangleCompatible0 (by omega)
  have hp25 := triangle_pair25_mem triangleCompatible0 (by omega)
  have hneq34 :
      (triangleFilter triangleTimeHalf).value
        (triangleCompatible0.enum (triangleIndex 2)) ≠
      (triangleFilter triangleTimeHalf).value
        (triangleCompatible0.enum (triangleIndex 3)) := by
    norm_num [triangleCompatible0, triangleOrder0, triangleOrder0Fun,
      triangleIndex, triangleFilter, triangleValue, triangleTimeHalf,
      triangleVertex1, triangleEdge01]
  have hneq25 :
      (triangleFilter triangleTimeHalf).value
        (triangleCompatible0.enum (triangleIndex 1)) ≠
      (triangleFilter triangleTimeHalf).value
        (triangleCompatible0.enum (triangleIndex 4)) := by
    norm_num [triangleCompatible0, triangleOrder0, triangleOrder0Fun,
      triangleIndex, triangleFilter, triangleValue, triangleTimeHalf,
      triangleVertex2, triangleEdge12]
    all_goals simp
    all_goals norm_num
  constructor
  · have hp := triangle_pair_point_in_dgm triangleCompatible0
      (triangleFilter triangleTimeHalf) triangle_half_order0_monotone
      (triangleIndex 2, triangleIndex 3) hp34 hneq34
    convert hp using 1;
      norm_num [triangleCompatible0, triangleOrder0, triangleOrder0Fun,
        triangleIndex, triangleFilter, triangleValue, triangleTimeHalf,
        triangleVertex1, triangleEdge01]
  · have hp := triangle_pair_point_in_dgm triangleCompatible0
      (triangleFilter triangleTimeHalf) triangle_half_order0_monotone
      (triangleIndex 1, triangleIndex 4) hp25 hneq25
    convert hp using 1;
      norm_num [triangleCompatible0, triangleOrder0, triangleOrder0Fun,
        triangleIndex, triangleFilter, triangleValue, triangleTimeHalf,
        triangleVertex2, triangleEdge12]; simp

set_option linter.unusedSimpArgs false in
private theorem triangle_time0_no_half_grade (σ : TotalFace triangleBoundary) :
    (triangleFilter triangleTime0).value σ ≠ (7 / 2 : ℝ) := by
  obtain ⟨i, rfl⟩ := triangleCompatible0.enum.surjective σ
  fin_cases i <;>
    norm_num [triangleCompatible0, triangleOrder0, triangleOrder0Fun,
      triangleFilter, triangleValue, triangleTime0,
      triangleVertex0, triangleVertex1, triangleVertex2,
      triangleEdge01, triangleEdge12, triangleEdge02] <;>
    simp [show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 2 by decide,
      show ({1, 2} : Finset (Fin 3)).card ≠ 1 by decide,
      show ({0, 2} : Finset (Fin 3)).card ≠ 1 by decide] <;>
    norm_num

/-- The triangle-boundary H₀ diagram moves along the interpolated
filter family: the crossing creates a finite death grade absent at time zero. -/
theorem triangle_diagram_path_nonconstant :
    dgm (ZMod 2) (triangleFilter triangleTime0) 0 ≠
      dgm (ZMod 2) (triangleFilter triangleTimeHalf) 0 := by
  intro heq
  have hpoint := triangle_midpoint_diagram_points.1
  rw [← heq] at hpoint
  obtain ⟨p, _, hdeath⟩ := dgm_finite_death_from_faceTemplate
    (ZMod 2) triangleCompatible0 (triangleFilter triangleTime0)
    triangleCompatible0.monotone 0 2 (7 / 2 : ℝ) hpoint
  exact triangle_time0_no_half_grade (triangleCompatible0.enum p.2) hdeath
#print axioms triangleValue_mono
#print axioms triangleBoundary_faceCount
#print axioms triangleOrder0Fun_bijective
#print axioms triangleOrder1Fun_bijective
#print axioms triangleCompatible0
#print axioms triangleCompatible1
#print axioms triangle_edge_values
#print axioms triangle_edge_order_crosses
#print axioms triangle_compatible_orders_reverse
#print axioms triangle_diagram_template
#print axioms triangle_explicit_endpoint_diagrams

end TDA.Persistence.Examples
