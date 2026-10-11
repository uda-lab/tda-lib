import TDA.Filtration.CompatibleOrderClosed
import TDA.Filtration.CompatibleOrderExistence
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

namespace TDA.Filtration.ClosedFixtures
open TDA.Simplicial
open TDA.Simplicial.FiniteComplex

private def emptyC : FiniteComplex 0 where
  faces := ∅
  nonempty := by decide
  downClosed := by decide

private def singleC : FiniteComplex 2 where
  faces := {{0}}
  nonempty := by decide
  downClosed := by decide

private def edgeC : FiniteComplex 2 where
  faces := {{0}, {1}, {0, 1}}
  nonempty := by decide
  downClosed := by decide

private theorem emptyCard : Fintype.card (TotalFace emptyC.toPre) = 0 := by decide

private theorem singleCard : Fintype.card (TotalFace singleC.toPre) = 1 := by decide

private def tied {n : ℕ} (C : FiniteComplex n) (r : ℝ) : FilterFunction C.toPre ℝ where
  value := fun _ => r
  mono := by intros; exact le_rfl

private noncomputable def emptyOrder : CompatibleOrder (tied emptyC 0) :=
  CompatibleOrder.ofLex emptyC (tied emptyC 0)

private theorem empty_complex_locus :
    {_x : ℝ | ∃ d : CompatibleOrder (tied emptyC 0), d.enum = emptyOrder.enum} = Set.univ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨emptyOrder, rfl⟩

private theorem empty_complex_continuous (s : TotalFace emptyC.toPre) :
    Continuous (fun _ : ℝ => (tied emptyC 0).value s) := continuous_const

private theorem empty_complex_closed :
    IsClosed {_x : ℝ | ∃ d : CompatibleOrder (tied emptyC 0),
      d.enum = emptyOrder.enum} := by
  rw [empty_complex_locus]
  exact isClosed_univ

private noncomputable def singleOrder : CompatibleOrder (tied singleC 0) :=
  CompatibleOrder.ofLex singleC (tied singleC 0)

private theorem empty_parameter_locus :
    {_x : Empty | ∃ d : CompatibleOrder (tied singleC 0), d.enum = singleOrder.enum} =
      Set.univ := by
  ext x
  exact x.elim

private theorem empty_parameter_continuous (s : TotalFace singleC.toPre) :
    Continuous (fun _ : Empty => (tied singleC 0).value s) := continuous_const

private theorem empty_parameter_closed :
    IsClosed {_x : Empty | ∃ d : CompatibleOrder (tied singleC 0),
      d.enum = singleOrder.enum} := by
  rw [empty_parameter_locus]
  exact isClosed_univ

private theorem tied_continuous {n : ℕ} (C : FiniteComplex n)
    (s : TotalFace C.toPre) :
    Continuous (fun x : ℝ => (tied C x).value s) := by
  change Continuous (fun x : ℝ => x)
  exact continuous_id

private theorem singleton_locus :
    {x : ℝ | ∃ d : CompatibleOrder (tied singleC x), d.enum = singleOrder.enum} =
      Set.univ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  refine ⟨singleOrder.transfer ?_, rfl⟩
  intro i j _
  exact le_rfl

private theorem singleton_closed :
    IsClosed {x : ℝ | ∃ d : CompatibleOrder (tied singleC x),
      d.enum = singleOrder.enum} := by
  rw [singleton_locus]
  exact isClosed_univ

private noncomputable def edgeOrder : CompatibleOrder (tied edgeC 0) :=
  CompatibleOrder.ofLex edgeC (tied edgeC 0)

private theorem tied_edge_locus :
    {x : ℝ | ∃ d : CompatibleOrder (tied edgeC x), d.enum = edgeOrder.enum} =
      Set.univ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  refine ⟨edgeOrder.transfer ?_, rfl⟩
  intro i j _
  exact le_rfl

private theorem tied_edge_closed :
    IsClosed {x : ℝ | ∃ d : CompatibleOrder (tied edgeC x),
      d.enum = edgeOrder.enum} := by
  rw [tied_edge_locus]
  exact isClosed_univ

private def edgeFamily (x : ℝ) : FilterFunction edgeC.toPre ℝ where
  value := fun s => if s.val = {0} then 0 else if s.val = {1} then x else max 0 x
  mono := by
    intro s t h
    have hs : s.val = {0} ∨ s.val = {1} ∨ s.val = {0,1} := by
      have hm : s.val ∈ edgeC.faces := s.property
      simpa [edgeC] using hm
    have ht : t.val = {0} ∨ t.val = {1} ∨ t.val = {0,1} := by
      have hm : t.val ∈ edgeC.faces := t.property
      simpa [edgeC] using hm
    rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht <;>
      simp_all [show ({0,1} : Finset (Fin 2)) ≠ {0} by decide,
        show ({0,1} : Finset (Fin 2)) ≠ {1} by decide]

private theorem edgeFamily_continuous (s : TotalFace edgeC.toPre) :
    Continuous (fun x : ℝ => (edgeFamily x).value s) := by
  change Continuous (fun x : ℝ => if s.val = {0} then 0 else
    if s.val = {1} then x else max 0 x)
  split_ifs
  · exact continuous_const
  · exact continuous_id
  · exact continuous_const.max continuous_id

private theorem edgeCard : Fintype.card (TotalFace edgeC.toPre) = 3 := by decide

private def edgeEnum3 : Fin 3 ≃ TotalFace edgeC.toPre where
  toFun := fun i =>
    (⟨if i = 0 then ({0} : Finset (Fin 2)) else if i = 1 then {1} else {0,1},
      by fin_cases i <;> decide⟩ : TotalFace edgeC.toPre)
  invFun := fun s => if s.val = ({0} : Finset (Fin 2)) then 0
    else if s.val = {1} then 1 else 2
  left_inv := by decide
  right_inv := by decide

private def edgeEnum : Fin (Fintype.card (TotalFace edgeC.toPre)) ≃
    TotalFace edgeC.toPre :=
  (Equiv.cast (congrArg Fin edgeCard)).trans edgeEnum3

private def fixedOrder : CompatibleOrder (tied edgeC 0) where
  enum := edgeEnum
  face_lt := by decide
  monotone := by intro i j _; exact le_rfl

private theorem fixedOrder_apply_cast (i : Fin 3) :
    fixedOrder.enum (Fin.cast edgeCard.symm i) = edgeEnum3 i := by
  change edgeEnum3 ((Equiv.cast (congrArg Fin edgeCard))
    ((Equiv.cast (congrArg Fin edgeCard)).symm i)) = edgeEnum3 i
  simp

private theorem fixedOrder_apply (i : Fin (Fintype.card (TotalFace edgeC.toPre))) :
    fixedOrder.enum i = edgeEnum3 (Fin.cast edgeCard i) := by
  have h := fixedOrder_apply_cast (Fin.cast edgeCard i)
  simpa only [Fin.cast_cast, Fin.cast_eq_self] using h

private theorem edgeEnum3_values (x : ℝ) :
    (edgeFamily x).value (edgeEnum3 0) = 0 ∧
    (edgeFamily x).value (edgeEnum3 1) = x ∧
    (edgeFamily x).value (edgeEnum3 2) = max 0 x := by
  simp [edgeFamily, edgeEnum3,
    show ({0,1} : Finset (Fin 2)) ≠ {0} by decide,
    show ({0,1} : Finset (Fin 2)) ≠ {1} by decide]

private theorem edgeEnum3_mono (x : ℝ) (hx : 0 ≤ x) :
    Monotone ((edgeFamily x).value ∘ edgeEnum3) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [edgeEnum3_values]

private theorem half_line_locus :
    {x : ℝ | ∃ d : CompatibleOrder (edgeFamily x), d.enum = fixedOrder.enum} =
      {x : ℝ | 0 ≤ x} := by
  ext x
  constructor
  · rintro ⟨d, hd⟩
    have h := d.monotone (show Fin.cast edgeCard.symm (0 : Fin 3) ≤
      Fin.cast edgeCard.symm (1 : Fin 3) by simp)
    rw [hd] at h
    change (edgeFamily x).value (fixedOrder.enum (Fin.cast edgeCard.symm 0)) ≤
      (edgeFamily x).value (fixedOrder.enum (Fin.cast edgeCard.symm 1)) at h
    rw [fixedOrder_apply_cast, fixedOrder_apply_cast] at h
    change 0 ≤ x
    simpa only [(edgeEnum3_values x).1, (edgeEnum3_values x).2.1] using h
  · intro hx
    refine ⟨fixedOrder.transfer ?_, rfl⟩
    intro i j hij
    have h := edgeEnum3_mono x hx ((Fin.cast_le_cast edgeCard).mpr hij)
    change (edgeFamily x).value (fixedOrder.enum i) ≤
      (edgeFamily x).value (fixedOrder.enum j)
    rw [fixedOrder_apply, fixedOrder_apply]
    exact h

private theorem half_line_closed :
    IsClosed {x : ℝ | ∃ d : CompatibleOrder (edgeFamily x),
      d.enum = fixedOrder.enum} := by
  exact fixedOrder.isClosed_compatible_locus edgeFamily edgeFamily_continuous

private theorem half_line_tie :
    ∃ d : CompatibleOrder (edgeFamily 0), d.enum = fixedOrder.enum := by
  have h : (0 : ℝ) ∈ {x : ℝ | 0 ≤ x} := by
    change (0 : ℝ) ≤ 0
    exact le_refl 0
  exact (Set.ext_iff.mp half_line_locus 0).mpr h

private theorem half_line_excludes_negative_one :
    ¬ ∃ d : CompatibleOrder (edgeFamily (-1)), d.enum = fixedOrder.enum := by
  intro h
  have hx := (Set.ext_iff.mp half_line_locus (-1)).mp h
  norm_num at hx

private theorem negative_one_has_other_order :
    ∃ d : CompatibleOrder (edgeFamily (-1)), d.enum ≠ fixedOrder.enum := by
  obtain ⟨d⟩ := exists_compatibleOrder (edgeFamily (-1))
  exact ⟨d, fun h => half_line_excludes_negative_one ⟨d, h⟩⟩

end TDA.Filtration.ClosedFixtures
