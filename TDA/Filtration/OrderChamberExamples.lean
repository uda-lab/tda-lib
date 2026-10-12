import TDA.Filtration.OrderChamberFilterFunction
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

namespace TDA.Filtration.OrderChamberExamples

open TDA.Filtration TDA.Simplicial TDA.Simplicial.FiniteComplex

universe u v w

-- 1. No coordinate or point is chosen.
private theorem empty_coordinates {X : Type u} [TopologicalSpace X]
    {β : Type v} (F : X → Fin 0 → β) :
    orderChamber F = Set.univ := by
  ext x
  simp [orderChamber, eqLocus]

-- 2. A varying single coordinate has no equality frontier.
private theorem singleton_coordinates {X : Type u} [TopologicalSpace X]
    {β : Type v} (F : X → Unit → β) :
    orderChamber F = Set.univ := by
  have h : ∀ i j : Unit, eqLocus F i j = Set.univ := by
    intro i j
    cases i; cases j
    simp [eqLocus]
  simp [orderChamber, h]

-- 3. The empty parameter space causes no hidden Nonempty requirement.
private theorem empty_parameters {ι : Type u} [Finite ι]
    {β : Type v} [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
    (F : Empty → ι → β)
    (hF : ∀ i, Continuous (fun x => F x i)) :
    IsOpen (orderChamber F) ∧ Dense (orderChamber F) ∧
      ∀ x₀ ∈ orderChamber F,
        ∃ U : Set Empty, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ orderChamber F ∧
          ∀ x ∈ U, ∀ i j,
            (F x₀ i ≤ F x₀ j ↔ F x i ≤ F x j) := by
  refine ⟨isOpen_orderChamber F, dense_orderChamber F hF, ?_⟩
  intro x₀ _
  exact x₀.elim

-- 4. Persistent ties can have varying grades.
private theorem persistent_ties {X : Type u} [TopologicalSpace X]
    {ι : Type v} {β : Type w} (g : X → β) :
    orderChamber (fun x (_ : ι) => g x) = Set.univ := by
  simp [orderChamber, eqLocus]

private theorem varying_tied_grades :
    orderChamber (fun x : ℝ => fun _ : Fin 2 => x) = Set.univ :=
  persistent_ties id

private theorem chamber_of_open_eq_status {X : Type u} [TopologicalSpace X]
    {ι : Type v} {β : Type w} [TopologicalSpace β] [T2Space β]
    (F : X → ι → β) (hF : ∀ i, Continuous (fun x => F x i))
    (x₀ : X) (U : Set X) (hUopen : IsOpen U) (hxU : x₀ ∈ U)
    (hstatus : ∀ y ∈ U, ∀ i j, F y i = F y j ↔ F x₀ i = F x₀ j) :
    x₀ ∈ orderChamber F := by
  intro hbad
  change x₀ ∈ ⋃ i, ⋃ j, frontier (eqLocus F i j) at hbad
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hbad
  obtain ⟨j, hfr⟩ := Set.mem_iUnion.mp hi
  by_cases heq : F x₀ i = F x₀ j
  · have hsub : U ⊆ eqLocus F i j := by
      intro y hy
      exact (hstatus y hy i j).mpr heq
    have hint : x₀ ∈ interior (eqLocus F i j) :=
      interior_maximal hsub hUopen hxU
    exact ((mem_interior_iff_notMem_frontier (s := eqLocus F i j) (x := x₀) heq).mp hint) hfr
  · have hclosed : IsClosed (eqLocus F i j) :=
      isClosed_eq (hF i) (hF j)
    exact heq (hclosed.frontier_subset hfr)

private def crossing (x : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 0 else x

-- 5. A crossing changes both weak-comparison directions at zero.
private theorem crossing_eq_locus : eqLocus crossing 0 1 = ({0} : Set ℝ) := by
  ext x
  simp [eqLocus, crossing]

private theorem crossing_continuous (i : Fin 2) :
    Continuous (fun x => crossing x i) := by
  fin_cases i
  · change Continuous (fun _ : ℝ => (0 : ℝ))
    exact continuous_const
  · change Continuous (fun x : ℝ => x)
    exact continuous_id

private theorem crossing_chamber :
    orderChamber crossing = ({0} : Set ℝ)ᶜ := by
  ext x
  constructor
  · intro hx hx0
    have hfr : frontier (eqLocus crossing 0 1) = ({0} : Set ℝ) := by
      rw [crossing_eq_locus, isClosed_singleton.frontier_eq, interior_singleton]
      simp
    have hbad : x ∈ frontier (eqLocus crossing 0 1) := by
      rw [hfr]
      exact hx0
    exact hx (Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨1, hbad⟩⟩)
  · intro hx
    have hne : x ≠ 0 := by simpa using hx
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · refine chamber_of_open_eq_status crossing crossing_continuous x
        (Set.Iio 0) isOpen_Iio hneg ?_
      intro y hy i j
      change y < 0 at hy
      have hy0 : y ≠ 0 := hy.ne
      fin_cases i <;> fin_cases j <;> simp_all [crossing, eq_comm]
    · refine chamber_of_open_eq_status crossing crossing_continuous x
        (Set.Ioi 0) isOpen_Ioi hpos ?_
      intro y hy i j
      change 0 < y at hy
      have hy0 : y ≠ 0 := hy.ne'
      fin_cases i <;> fin_cases j <;> simp_all [crossing, eq_comm]

private theorem crossing_weak_orders_differ :
    ¬ (∀ i j : Fin 2, crossing (-1) i ≤ crossing (-1) j ↔
      crossing 1 i ≤ crossing 1 j) := by
  intro h
  have h01 := h 0 1
  norm_num [crossing] at h01

private theorem crossing_no_stable_open_zero :
    ¬ ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
      ∀ x ∈ U, ∀ i j : Fin 2,
        (crossing 0 i ≤ crossing 0 j ↔ crossing x i ≤ crossing x j) := by
  rintro ⟨U, hopen, hzero, hcomp⟩
  have hsubset : U ⊆ ({0} : Set ℝ) := by
    intro x hx
    have h01 := (hcomp x hx 0 1).mp (by norm_num [crossing])
    have h10 := (hcomp x hx 1 0).mp (by norm_num [crossing])
    have : x = 0 := le_antisymm (by simpa [crossing] using h10)
      (by simpa [crossing] using h01)
    simpa using this
  have hmem : (0 : ℝ) ∈ interior ({0} : Set ℝ) :=
    interior_maximal hsubset hopen hzero
  simp [interior_singleton] at hmem

-- 6. Equality on a half-line is retained on its open interior.
private def openTie (x : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then 0 else if i = 1 then x else |x|

private theorem open_tie_eq_locus :
    eqLocus openTie 1 2 = Set.Ici 0 := by
  ext x
  change x = |x| ↔ 0 ≤ x
  exact eq_comm.trans abs_eq_self

private theorem open_tie_continuous (i : Fin 3) :
    Continuous (fun x => openTie x i) := by
  fin_cases i
  · change Continuous (fun _ : ℝ => (0 : ℝ))
    exact continuous_const
  · change Continuous (fun x : ℝ => x)
    exact continuous_id
  · change Continuous (fun x : ℝ => |x|)
    exact continuous_id.abs

private theorem open_tie_chamber :
    orderChamber openTie = ({0} : Set ℝ)ᶜ := by
  ext x
  constructor
  · intro hx hx0
    have hfr : frontier (eqLocus openTie 1 2) = ({0} : Set ℝ) := by
      rw [open_tie_eq_locus, frontier_Ici]
    have hbad : x ∈ frontier (eqLocus openTie 1 2) := by
      rw [hfr]
      exact hx0
    exact hx (Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨2, hbad⟩⟩)
  · intro hx
    have hne : x ≠ 0 := by simpa using hx
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · refine chamber_of_open_eq_status openTie open_tie_continuous x
        (Set.Iio 0) isOpen_Iio hneg ?_
      intro y hy i j
      change y < 0 at hy
      have hy0 : y ≠ 0 := hy.ne
      have hxneg : x ≠ -x := by intro h; linarith
      have hyneg : y ≠ -y := by intro h; linarith
      fin_cases i <;> fin_cases j <;>
        simp_all [openTie, abs_of_neg hneg, abs_of_neg hy, eq_comm]
    · refine chamber_of_open_eq_status openTie open_tie_continuous x
        (Set.Ioi 0) isOpen_Ioi hpos ?_
      intro y hy i j
      change 0 < y at hy
      have hy0 : y ≠ 0 := hy.ne'
      fin_cases i <;> fin_cases j <;>
        simp_all [openTie, abs_of_nonneg hpos.le, abs_of_nonneg hy.le, eq_comm]

private theorem open_tie_positive_values (x : ℝ) (hx : 0 < x) :
    openTie x 1 = openTie x 2 ∧ openTie x 0 < openTie x 1 := by
  simp [openTie, abs_of_nonneg hx.le, hx]

private theorem open_tie_negative_values (x : ℝ) (hx : x < 0) :
    openTie x 1 < openTie x 0 ∧ openTie x 0 < openTie x 2 := by
  simp [openTie, abs_of_neg hx, hx]

private theorem open_tie_one_mem : (1 : ℝ) ∈ orderChamber openTie := by
  rw [open_tie_chamber]
  norm_num

private theorem open_tie_zero_not_mem : (0 : ℝ) ∉ orderChamber openTie := by
  rw [open_tie_chamber]
  simp

-- 7. Relative topology uses the subtype's own frontiers.
private def nonnegativeDomain : Set ℝ := Set.Ici 0

private def restrictedTie (x : nonnegativeDomain) (i : Fin 2) : ℝ :=
  if i = 0 then x.val else |x.val|

private theorem relative_tie (x : nonnegativeDomain) (i : Fin 2) :
    restrictedTie x i = x.val := by
  have hx := x.property
  change (0 : ℝ) ≤ x.val at hx
  fin_cases i <;> simp [restrictedTie, abs_of_nonneg hx]

private theorem relative_chamber :
    orderChamber restrictedTie = Set.univ := by
  simp [orderChamber, eqLocus, relative_tie]

private theorem relative_contains_zero :
    (⟨0, by change (0 : ℝ) ≤ 0; exact le_rfl⟩ : nonnegativeDomain) ∈ orderChamber restrictedTie := by
  rw [relative_chamber]
  exact Set.mem_univ _

private def ambientTwo (x : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then x else |x|

private theorem ambient_two_eq_locus :
    eqLocus ambientTwo 0 1 = Set.Ici 0 := by
  ext x
  change x = |x| ↔ 0 ≤ x
  exact eq_comm.trans abs_eq_self

private theorem ambient_two_continuous (i : Fin 2) :
    Continuous (fun x => ambientTwo x i) := by
  fin_cases i
  · change Continuous (fun x : ℝ => x)
    exact continuous_id
  · change Continuous (fun x : ℝ => |x|)
    exact continuous_id.abs

private theorem ambient_two_chamber :
    orderChamber ambientTwo = ({0} : Set ℝ)ᶜ := by
  ext x
  constructor
  · intro hx hx0
    have hfr : frontier (eqLocus ambientTwo 0 1) = ({0} : Set ℝ) := by
      rw [ambient_two_eq_locus, frontier_Ici]
    have hbad : x ∈ frontier (eqLocus ambientTwo 0 1) := by
      rw [hfr]
      exact hx0
    exact hx (Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨1, hbad⟩⟩)
  · intro hx
    have hne : x ≠ 0 := by simpa using hx
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · refine chamber_of_open_eq_status ambientTwo ambient_two_continuous x
        (Set.Iio 0) isOpen_Iio hneg ?_
      intro y hy i j
      change y < 0 at hy
      have hy0 : y ≠ 0 := hy.ne
      have hxneg : x ≠ -x := by intro h; linarith
      have hyneg : y ≠ -y := by intro h; linarith
      fin_cases i <;> fin_cases j <;>
        simp_all [ambientTwo, abs_of_neg hneg, abs_of_neg hy, eq_comm]
    · refine chamber_of_open_eq_status ambientTwo ambient_two_continuous x
        (Set.Ioi 0) isOpen_Ioi hpos ?_
      intro y hy i j
      change 0 < y at hy
      have hy0 : y ≠ 0 := hy.ne'
      fin_cases i <;> fin_cases j <;>
        simp_all [ambientTwo, abs_of_nonneg hpos.le, abs_of_nonneg hy.le, eq_comm]

private theorem ambient_boundary_excluded :
    (0 : ℝ) ∉ orderChamber ambientTwo := by
  rw [ambient_two_chamber]
  simp

private theorem arbitrary_relative_domain {E : Type u} [TopologicalSpace E]
    (D : Set E) {ι : Type v} [Finite ι] {β : Type w}
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
    (F : D → ι → β) (hF : ∀ i, Continuous (fun x => F x i)) :
    IsOpen (orderChamber F) ∧ Dense (orderChamber F) ∧
      ∀ x₀ ∈ orderChamber F,
        ∃ U : Set D, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ orderChamber F ∧
          ∀ x ∈ U, ∀ i j,
            (F x₀ i ≤ F x₀ j ↔ F x i ≤ F x j) := by
  exact ⟨isOpen_orderChamber F, dense_orderChamber F hF,
    fun _ hx => exists_open_le_iff_of_mem_orderChamber F hF hx⟩

-- 8. An actual edge filter, with an explicitly supplied face enumeration.
private def edgeC : FiniteComplex 2 where
  faces := {{0}, {1}, {0, 1}}
  nonempty := by decide
  downClosed := by decide

private def edgeV0 : TotalFace edgeC.toPre := ⟨{0}, by decide⟩
private def edgeV1 : TotalFace edgeC.toPre := ⟨{1}, by decide⟩
private def edgeFace : TotalFace edgeC.toPre := ⟨{0, 1}, by decide⟩

private def edgeFamily (x : ℝ) : FilterFunction edgeC.toPre ℝ where
  value := fun s => if s.val = {0} then 0 else if s.val = {1} then x else max 0 x
  mono := by
    intro s t h
    have hs : s.val = {0} ∨ s.val = {1} ∨ s.val = {0,1} := by
      have hm := s.property
      change s.val ∈ edgeC.faces at hm
      simpa [edgeC] using hm
    have ht : t.val = {0} ∨ t.val = {1} ∨ t.val = {0,1} := by
      have hm := t.property
      change t.val ∈ edgeC.faces at hm
      simpa [edgeC] using hm
    rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht <;>
      simp_all [show ({0,1} : Finset (Fin 2)) ≠ {0} by decide,
        show ({0,1} : Finset (Fin 2)) ≠ {1} by decide]

private theorem edge_family_continuous (s : TotalFace edgeC.toPre) :
    Continuous (fun x : ℝ => (edgeFamily x).value s) := by
  change Continuous (fun x : ℝ => if s.val = {0} then 0 else
    if s.val = {1} then x else max 0 x)
  split_ifs
  · exact continuous_const
  · exact continuous_id
  · exact continuous_const.max continuous_id

private theorem edge_card : Fintype.card (TotalFace edgeC.toPre) = 3 := by decide

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
  (Equiv.cast (congrArg Fin edge_card)).trans edgeEnum3

private theorem edge_enum_apply (i : Fin 3) :
    edgeEnum (Fin.cast edge_card.symm i) = edgeEnum3 i := by
  change edgeEnum3 ((Equiv.cast (congrArg Fin edge_card))
    ((Equiv.cast (congrArg Fin edge_card)).symm i)) = edgeEnum3 i
  simp

private theorem edge_enum_apply_index
    (i : Fin (Fintype.card (TotalFace edgeC.toPre))) :
    edgeEnum i = edgeEnum3 (Fin.cast edge_card i) := by
  have h := edge_enum_apply (Fin.cast edge_card i)
  simpa only [Fin.cast_cast, Fin.cast_eq_self] using h

private theorem edge_values (x : ℝ) :
    (edgeFamily x).value edgeV0 = 0 ∧
    (edgeFamily x).value edgeV1 = x ∧
    (edgeFamily x).value edgeFace = max 0 x := by
  simp [edgeFamily, edgeV0, edgeV1, edgeFace,
    show ({0,1} : Finset (Fin 2)) ≠ {0} by decide,
    show ({0,1} : Finset (Fin 2)) ≠ {1} by decide]

private theorem edge_positive_same_weak_order (x : ℝ) (hx : 0 < x) :
    OrderingEquivalent (edgeFamily 1) (edgeFamily x) := by
  have hxle : 0 ≤ x := hx.le
  intro s t
  have hs : s.val = {0} ∨ s.val = {1} ∨ s.val = {0,1} := by
    have hm := s.property
    change s.val ∈ edgeC.faces at hm
    simpa [edgeC] using hm
  have ht : t.val = {0} ∨ t.val = {1} ∨ t.val = {0,1} := by
    have hm := t.property
    change t.val ∈ edgeC.faces at hm
    simpa [edgeC] using hm
  rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht <;>
    simp_all [edgeFamily,
      show ({0,1} : Finset (Fin 2)) ≠ {0} by decide] <;>
      norm_num <;> exact hx

private theorem edge_family_one_chamber :
    (1 : ℝ) ∈ orderChamber (fun x s => (edgeFamily x).value s) := by
  apply chamber_of_open_eq_status
    (fun x s => (edgeFamily x).value s) edge_family_continuous
    1 (Set.Ioi 0) isOpen_Ioi (by norm_num)
  intro y hy s t
  have h := (edge_positive_same_weak_order y hy).value_eq_iff s t
  exact h.symm

private theorem edge_positive_open_neighborhood :
    IsOpen (Set.Ioi (0 : ℝ)) ∧ (1 : ℝ) ∈ Set.Ioi 0 ∧
      Set.Ioi (0 : ℝ) ⊆
        orderChamber (fun x s => (edgeFamily x).value s) ∧
      ∀ x ∈ Set.Ioi (0 : ℝ),
        OrderingEquivalent (edgeFamily 1) (edgeFamily x) := by
  refine ⟨isOpen_Ioi, by norm_num, ?_, ?_⟩
  · intro x hx
    apply chamber_of_open_eq_status
      (fun y s => (edgeFamily y).value s) edge_family_continuous
      x (Set.Ioi 0) isOpen_Ioi hx
    intro y hy s t
    have h := (edge_positive_same_weak_order x hx).value_eq_iff s t
    have h' := (edge_positive_same_weak_order y hy).value_eq_iff s t
    exact h'.symm.trans h
  · intro x hx
    exact edge_positive_same_weak_order x hx

private def edgeOrderOne : CompatibleOrder (edgeFamily 1) where
  enum := edgeEnum
  face_lt := by decide
  monotone := by
    have hbase : Monotone ((edgeFamily 1).value ∘ edgeEnum3) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [edgeEnum3, edgeFamily,
          show ({0, 1} : Finset (Fin 2)) ≠ {0} by decide]
    intro i j hij
    change (edgeFamily 1).value (edgeEnum i) ≤
      (edgeFamily 1).value (edgeEnum j)
    rw [edge_enum_apply_index, edge_enum_apply_index]
    exact hbase ((Fin.cast_le_cast edge_card).mpr hij)

private theorem edge_positive_neighborhood :
    ∃ U : Set ℝ, IsOpen U ∧ (1 : ℝ) ∈ U ∧
      U ⊆ orderChamber (fun x s => (edgeFamily x).value s) ∧
      ∀ x ∈ U, OrderingEquivalent (edgeFamily 1) (edgeFamily x) :=
  FilterFunction.exists_open_orderingEquivalent_of_mem_orderChamber
    edgeFamily edge_family_continuous edge_family_one_chamber

private theorem edge_same_enum :
    ∃ U : Set ℝ, IsOpen U ∧ (1 : ℝ) ∈ U ∧
      U ⊆ orderChamber (fun x s => (edgeFamily x).value s) ∧
      ∀ x ∈ U, ∃ d : CompatibleOrder (edgeFamily x), d.enum = edgeOrderOne.enum :=
  CompatibleOrder.exists_open_sameEnum_of_mem_orderChamber
    edgeFamily edge_family_continuous edge_family_one_chamber edgeOrderOne

private theorem edge_zero_same_enum :
    ∃ d : CompatibleOrder (edgeFamily 0), d.enum = edgeOrderOne.enum := by
  refine ⟨edgeOrderOne.transfer ?_, rfl⟩
  intro i j _
  simp [edgeFamily]

private theorem edge_zero_not_chamber :
    (0 : ℝ) ∉ orderChamber (fun x s => (edgeFamily x).value s) := by
  have heq : eqLocus (fun x s => (edgeFamily x).value s) edgeV0 edgeV1 =
      ({0} : Set ℝ) := by
    ext x
    simp [eqLocus, edge_values]
  have hfr : frontier (eqLocus (fun x s => (edgeFamily x).value s)
      edgeV0 edgeV1) = ({0} : Set ℝ) := by
    rw [heq, isClosed_singleton.frontier_eq, interior_singleton]
    simp
  intro hx
  have hbad : (0 : ℝ) ∈ frontier (eqLocus
      (fun x s => (edgeFamily x).value s) edgeV0 edgeV1) := by
    rw [hfr]
    simp
  exact hx (Set.mem_iUnion.mpr
    ⟨edgeV0, Set.mem_iUnion.mpr ⟨edgeV1, hbad⟩⟩)

private theorem edge_zero_no_stable_open :
    ¬ ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
      ∀ x ∈ U, OrderingEquivalent (edgeFamily 0) (edgeFamily x) := by
  rintro ⟨U, hopen, hzero, hcomp⟩
  have hsubset : U ⊆ ({0} : Set ℝ) := by
    intro x hx
    have h01 := (hcomp x hx edgeV0 edgeV1).mp (by simp [edge_values])
    have h10 := (hcomp x hx edgeV1 edgeV0).mp (by simp [edge_values])
    have hxeq : x = 0 := le_antisymm
      (by simpa [edge_values] using h10)
      (by simpa [edge_values] using h01)
    simpa using hxeq
  have hmem : (0 : ℝ) ∈ interior ({0} : Set ℝ) :=
    interior_maximal hsubset hopen hzero
  simp [interior_singleton] at hmem

private theorem edge_negative_incompatible :
    ¬ ∃ d : CompatibleOrder (edgeFamily (-1)), d.enum = edgeOrderOne.enum := by
  rintro ⟨d, hd⟩
  have h := d.monotone (show Fin.cast edge_card.symm (0 : Fin 3) ≤
    Fin.cast edge_card.symm (1 : Fin 3) by simp)
  rw [hd] at h
  change (edgeFamily (-1)).value (edgeOrderOne.enum (Fin.cast edge_card.symm 0)) ≤
    (edgeFamily (-1)).value (edgeOrderOne.enum (Fin.cast edge_card.symm 1)) at h
  simp [edgeOrderOne, edge_enum_apply, edgeEnum3, edgeFamily] at h
  norm_num at h

private def oppositeEnum3 : Fin 3 ≃ TotalFace edgeC.toPre where
  toFun := fun i =>
    (⟨if i = 0 then ({1} : Finset (Fin 2)) else if i = 1 then {0} else {0,1},
      by fin_cases i <;> decide⟩ : TotalFace edgeC.toPre)
  invFun := fun s => if s.val = ({1} : Finset (Fin 2)) then 0
    else if s.val = {0} then 1 else 2
  left_inv := by decide
  right_inv := by decide

private def oppositeEnum : Fin (Fintype.card (TotalFace edgeC.toPre)) ≃
    TotalFace edgeC.toPre :=
  (Equiv.cast (congrArg Fin edge_card)).trans oppositeEnum3

private def tiedEdge (x : ℝ) : FilterFunction edgeC.toPre ℝ where
  value := fun _ => x
  mono := by intros; exact le_rfl

private def oppositeOrder : CompatibleOrder (tiedEdge 1) where
  enum := oppositeEnum
  face_lt := by decide
  monotone := by intro i j _; exact le_rfl

private theorem opposite_first_face :
    (oppositeOrder.enum (Fin.cast edge_card.symm 0)).val =
      ({1} : Finset (Fin 2)) := by decide

private theorem opposite_supplied_enum :
    ∃ U : Set ℝ, IsOpen U ∧ (1 : ℝ) ∈ U ∧
      U ⊆ orderChamber (fun x s => (tiedEdge x).value s) ∧
      ∀ x ∈ U, ∃ d : CompatibleOrder (tiedEdge x), d.enum = oppositeOrder.enum := by
  exact CompatibleOrder.exists_open_sameEnum_of_mem_orderChamber tiedEdge
    (fun _ => by
      change Continuous (fun x : ℝ => x)
      exact continuous_id)
    (by
      rw [show orderChamber (fun x s => (tiedEdge x).value s) = Set.univ from
        persistent_ties id]
      exact Set.mem_univ _)
    oppositeOrder

-- The required constant family is independent of the parameter as well as the face.
-- Keep the varying-grade tiedEdge example above as a separate fixture.
private def parameterConstantTiedEdge (_x : ℝ) : FilterFunction edgeC.toPre ℝ where
  value := fun _ => 0
  mono := by intros; exact le_rfl

private theorem parameter_constant_tied_filter (x y : ℝ) :
    parameterConstantTiedEdge x = parameterConstantTiedEdge y := rfl

private theorem parameter_constant_tied_grades (x : ℝ) (s : TotalFace edgeC.toPre) :
    (parameterConstantTiedEdge x).value s = 0 := rfl

private theorem parameter_constant_tied_continuous (s : TotalFace edgeC.toPre) :
    Continuous (fun x : ℝ => (parameterConstantTiedEdge x).value s) :=
  continuous_const

private theorem parameter_constant_tied_chamber :
    orderChamber (fun x s => (parameterConstantTiedEdge x).value s) = Set.univ :=
  persistent_ties (fun _ : ℝ => (0 : ℝ))

private def parameterConstantOppositeOrder :
    CompatibleOrder (parameterConstantTiedEdge 1) where
  enum := oppositeEnum
  face_lt := by decide
  monotone := by intro i j _; exact le_rfl

private theorem parameter_constant_opposite_faces :
    (parameterConstantOppositeOrder.enum (Fin.cast edge_card.symm 0)).val =
      ({1} : Finset (Fin 2)) ∧
    (parameterConstantOppositeOrder.enum (Fin.cast edge_card.symm 1)).val =
      ({0} : Finset (Fin 2)) ∧
    (parameterConstantOppositeOrder.enum (Fin.cast edge_card.symm 2)).val =
      ({0, 1} : Finset (Fin 2)) := by decide

private theorem parameter_constant_opposite_supplied_enum :
    ∃ U : Set ℝ, IsOpen U ∧ (1 : ℝ) ∈ U ∧
      U ⊆ orderChamber (fun x s => (parameterConstantTiedEdge x).value s) ∧
      ∀ x ∈ U, ∃ d : CompatibleOrder (parameterConstantTiedEdge x),
        d.enum = parameterConstantOppositeOrder.enum := by
  exact CompatibleOrder.exists_open_sameEnum_of_mem_orderChamber
    parameterConstantTiedEdge parameter_constant_tied_continuous
    (by rw [parameter_constant_tied_chamber]; exact Set.mem_univ _)
    parameterConstantOppositeOrder

end TDA.Filtration.OrderChamberExamples
