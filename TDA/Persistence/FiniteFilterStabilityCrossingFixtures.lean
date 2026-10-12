import TDA.Persistence.FiniteFilterStability
import TDA.Simplicial.FiniteComplex

set_option autoImplicit false

/-! Concrete finite-filter crossing fixtures on three actual isolated vertices. -/

namespace TDA.Persistence.StabilityCrossingFixtures

open TDA.Simplicial TDA.Filtration TDA.Persistence

private def threePoints : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s.card ≤ 1}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, (Finset.card_le_card hts).trans hs.2⟩

private instance threePointsFaces : Fintype (TotalFace threePoints) := by
  change Fintype {s : Finset (Fin 3) // s.Nonempty ∧ s.card ≤ 1}
  infer_instance

private def v0 : TotalFace threePoints :=
  ⟨{0}, by change ({0} : Finset (Fin 3)).Nonempty ∧ _; decide⟩
private def v1 : TotalFace threePoints :=
  ⟨{1}, by change ({1} : Finset (Fin 3)).Nonempty ∧ _; decide⟩
private def v2 : TotalFace threePoints :=
  ⟨{2}, by change ({2} : Finset (Fin 3)).Nonempty ∧ _; decide⟩

private theorem threePoints_cases (s : TotalFace threePoints) :
    s = v0 ∨ s = v1 ∨ s = v2 := by
  have classify : ∀ q : Finset (Fin 3), q.Nonempty → q.card ≤ 1 →
      q = {0} ∨ q = {1} ∨ q = {2} := by decide
  have hc := classify s.1 s.2.1 s.2.2
  rcases hc with h | h | h <;> simp_all [v0, v1, v2, Subtype.ext_iff]

/-- An actual real filter on three isolated vertices. -/
def threePointFilter (a b c : ℝ) : FilterFunction threePoints ℝ where
  value s := if s = v0 then a else if s = v1 then b else c
  mono := by
    intro s t hst
    rcases threePoints_cases s with hs | hs | hs <;>
      rcases threePoints_cases t with ht | ht | ht <;>
      subst s <;> subst t <;>
      simp_all [v0, v1, v2]

private theorem vertex_values (a b c : ℝ) :
    (threePointFilter a b c).value v0 = a ∧
    (threePointFilter a b c).value v1 = b ∧
    (threePointFilter a b c).value v2 = c := by
  simp [threePointFilter, v0, v1, v2]

private def beforeFilter : FilterFunction threePoints ℝ :=
  threePointFilter 0 0 1

private def afterFilter : FilterFunction threePoints ℝ :=
  threePointFilter 1 1 0

private def endpointBefore : FilterFunction threePoints ℝ :=
  threePointFilter 0 0 2

private def endpointAfter : FilterFunction threePoints ℝ :=
  threePointFilter 0 1 2

private noncomputable def half : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by constructor <;> norm_num⟩
private def zero : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
private def one : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

private def forwardFun (i : Fin (faceCount threePoints)) : TotalFace threePoints :=
  if i.val = 0 then v0 else if i.val = 1 then v1 else v2

private def reverseFun (i : Fin (faceCount threePoints)) : TotalFace threePoints :=
  if i.val = 0 then v2 else if i.val = 1 then v0 else v1

private theorem forwardFun_bijective : Function.Bijective forwardFun := by decide
private theorem reverseFun_bijective : Function.Bijective reverseFun := by decide

private noncomputable def forwardOrder : Fin (faceCount threePoints) ≃
    TotalFace threePoints :=
  Equiv.ofBijective forwardFun forwardFun_bijective

private noncomputable def reverseOrder : Fin (faceCount threePoints) ≃
    TotalFace threePoints :=
  Equiv.ofBijective reverseFun reverseFun_bijective

private theorem forward_face_lt :
    ∀ i j : Fin (faceCount threePoints),
      (forwardOrder i).val ⊂ (forwardOrder j).val → i < j := by
  decide

private theorem reverse_face_lt :
    ∀ i j : Fin (faceCount threePoints),
      (reverseOrder i).val ⊂ (reverseOrder j).val → i < j := by
  decide

private theorem forward_endpoint_mono (t : Set.Icc (0 : ℝ) 1) :
    Monotone ((intervalFilter endpointBefore endpointAfter t).value ∘ forwardOrder) := by
  intro i j hij
  have hij' := Fin.le_def.mp hij
  fin_cases i <;> fin_cases j <;>
    norm_num [forwardOrder, forwardFun, intervalFilter_value, endpointBefore,
      endpointAfter, vertex_values] at *
  all_goals have := t.2.1; have := t.2.2; first | omega | linarith

private theorem forward_before_mono (t : Set.Icc (0 : ℝ) 1)
    (ht : (t : ℝ) ≤ 1 / 2) :
    Monotone ((intervalFilter beforeFilter afterFilter t).value ∘ forwardOrder) := by
  intro i j hij
  have hij' := Fin.le_def.mp hij
  fin_cases i <;> fin_cases j <;>
    norm_num [forwardOrder, forwardFun, intervalFilter_value,
      beforeFilter, afterFilter, vertex_values] at *
  all_goals first | omega | linarith

private theorem reverse_after_mono (t : Set.Icc (0 : ℝ) 1)
    (ht : 1 / 2 ≤ (t : ℝ)) :
    Monotone ((intervalFilter beforeFilter afterFilter t).value ∘ reverseOrder) := by
  intro i j hij
  have hij' := Fin.le_def.mp hij
  fin_cases i <;> fin_cases j <;>
    norm_num [reverseOrder, reverseFun, intervalFilter_value,
      beforeFilter, afterFilter, vertex_values] at *
  all_goals first | omega | linarith

private noncomputable def endpointOrder :
    CompatibleOrder (intervalFilter endpointBefore endpointAfter half) where
  enum := forwardOrder
  face_lt := forward_face_lt
  monotone := forward_endpoint_mono half

private noncomputable def beforeOrder :
    CompatibleOrder (intervalFilter beforeFilter afterFilter half) where
  enum := forwardOrder
  face_lt := forward_face_lt
  monotone := forward_before_mono half (by norm_num [half])

private noncomputable def afterOrder :
    CompatibleOrder (intervalFilter beforeFilter afterFilter half) where
  enum := reverseOrder
  face_lt := reverse_face_lt
  monotone := reverse_after_mono half (by norm_num [half])

/-- The endpoint tie admits one face-compatible enumeration on the whole
closed interpolation interval, including the tied left endpoint. -/
theorem endpoint_crossing_closed_order :
    ∃ e : CompatibleOrder (intervalFilter endpointBefore endpointAfter half),
      ∀ t : Set.Icc (0 : ℝ) 1,
        Monotone ((intervalFilter endpointBefore endpointAfter t).value ∘ e.enum) :=
  ⟨endpointOrder, forward_endpoint_mono⟩

/-- A midpoint tie admits both adjacent orders: each remains compatible at
the shared closed endpoint while the strict order reverses across it. -/
theorem simultaneous_crossing_closed_orders :
    (∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ≤ 1 / 2 →
      Monotone ((intervalFilter beforeFilter afterFilter t).value ∘ beforeOrder.enum)) ∧
    (∀ t : Set.Icc (0 : ℝ) 1, 1 / 2 ≤ (t : ℝ) →
      Monotone ((intervalFilter beforeFilter afterFilter t).value ∘ afterOrder.enum)) :=
  ⟨forward_before_mono, reverse_after_mono⟩

/-- Two different actual face pairs cross simultaneously at the midpoint,
while the first two faces are tied for the whole interpolation. -/
theorem persistent_tie_and_simultaneous_crossing :
    (∀ t : Set.Icc (0 : ℝ) 1,
      (intervalFilter beforeFilter afterFilter t).value v0 =
        (intervalFilter beforeFilter afterFilter t).value v1) ∧
    (intervalFilter beforeFilter afterFilter half).value v0 =
      (intervalFilter beforeFilter afterFilter half).value v2 ∧
    (intervalFilter beforeFilter afterFilter half).value v1 =
      (intervalFilter beforeFilter afterFilter half).value v2 ∧
    (intervalFilter beforeFilter afterFilter zero).value v0 <
      (intervalFilter beforeFilter afterFilter zero).value v2 ∧
    (intervalFilter beforeFilter afterFilter one).value v2 <
      (intervalFilter beforeFilter afterFilter one).value v0 := by
  simp [intervalFilter_value, beforeFilter, afterFilter, vertex_values,
    half, zero, one]
  norm_num

/-- Two actual face values meet at the left endpoint and separate on the
interior, with no strict order forced at the endpoint. -/
theorem crossing_at_left_endpoint :
    (intervalFilter endpointBefore endpointAfter zero).value v0 =
      (intervalFilter endpointBefore endpointAfter zero).value v1 ∧
    (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) →
      (intervalFilter endpointBefore endpointAfter t).value v0 <
        (intervalFilter endpointBefore endpointAfter t).value v1) := by
  constructor
  · simp [intervalFilter_value, endpointBefore, endpointAfter, vertex_values, zero]
  · intro t ht
    simpa [intervalFilter_value, endpointBefore, endpointAfter, vertex_values] using ht

end TDA.Persistence.StabilityCrossingFixtures
