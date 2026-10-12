import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Baire.Lemmas

set_option autoImplicit false

universe u v w

namespace TDA.Filtration

variable {X : Type u} {ι : Type v} {β : Type w}

def eqLocus (F : X → ι → β) (i j : ι) : Set X :=
  {x | F x i = F x j}

variable [TopologicalSpace X]

def orderChamber (F : X → ι → β) : Set X :=
  (⋃ i, ⋃ j, frontier (eqLocus F i j))ᶜ

theorem isOpen_orderChamber [Finite ι] (F : X → ι → β) :
    IsOpen (orderChamber F) := by
  unfold orderChamber
  exact (isClosed_iUnion_of_finite fun i =>
    isClosed_iUnion_of_finite fun j => isClosed_frontier).isOpen_compl

variable [Finite ι] [LinearOrder β] [TopologicalSpace β]
  [OrderClosedTopology β]

theorem dense_orderChamber
    (F : X → ι → β)
    (hF : ∀ i, Continuous (fun x => F x i)) :
    Dense (orderChamber F) := by
  let G : ι × ι → Set X := fun p => (frontier (eqLocus F p.1 p.2))ᶜ
  have hGopen : ∀ p, IsOpen (G p) := by
    intro p
    exact isClosed_frontier.isOpen_compl
  have hGdense : ∀ p, Dense (G p) := by
    intro p
    have hclosed : IsClosed (eqLocus F p.1 p.2) :=
      isClosed_eq (hF p.1) (hF p.2)
    exact interior_eq_empty_iff_dense_compl.mp (interior_frontier hclosed)
  have hinter : Dense (⋂₀ Set.range G) :=
    (Set.finite_range G).dense_sInter
      (by rintro s ⟨p, rfl⟩; exact hGopen p)
      (by rintro s ⟨p, rfl⟩; exact hGdense p)
  have heq : orderChamber F = ⋂₀ Set.range G := by
    ext x
    rw [Set.sInter_range]
    constructor
    · intro hx
      refine Set.mem_iInter.mpr fun p => ?_
      change x ∉ frontier (eqLocus F p.1 p.2)
      intro hfr
      exact hx (Set.mem_iUnion.mpr
        ⟨p.1, Set.mem_iUnion.mpr ⟨p.2, hfr⟩⟩)
    · intro hx
      change x ∉ ⋃ i, ⋃ j, frontier (eqLocus F i j)
      intro hbad
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hbad
      obtain ⟨j, hfr⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iInter.mp hx (i, j) hfr
  rw [heq]
  exact hinter

theorem exists_open_le_iff_of_mem_orderChamber
    (F : X → ι → β)
    (hF : ∀ i, Continuous (fun x => F x i))
    {x₀ : X} (hx₀ : x₀ ∈ orderChamber F) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ orderChamber F ∧
      ∀ x ∈ U, ∀ i j,
        (F x₀ i ≤ F x₀ j ↔ F x i ≤ F x j) := by
  classical
  have hpair : ∀ i j : ι, ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧
      ∀ x ∈ W, (F x₀ i ≤ F x₀ j ↔ F x i ≤ F x j) := by
    intro i j
    rcases lt_trichotomy (F x₀ i) (F x₀ j) with hij | heq | hji
    · refine ⟨{x | F x i < F x j}, isOpen_lt (hF i) (hF j), hij, ?_⟩
      intro x hx
      exact iff_of_true hij.le hx.le
    · have hnot : x₀ ∉ frontier (eqLocus F i j) := by
        intro hfront
        exact hx₀ (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hfront⟩⟩)
      have hmem : x₀ ∈ interior (eqLocus F i j) :=
        (mem_interior_iff_notMem_frontier (show x₀ ∈ eqLocus F i j from heq)).mpr hnot
      refine ⟨interior (eqLocus F i j), isOpen_interior, hmem, ?_⟩
      intro x hx
      have hval : F x i = F x j :=
        (interior_subset (s := eqLocus F i j)) hx
      exact iff_of_true heq.le hval.le
    · refine ⟨{x | F x j < F x i}, isOpen_lt (hF j) (hF i), hji, ?_⟩
      intro x hx
      exact iff_of_false (not_le_of_gt hji) (not_le_of_gt hx)
  let W : ι × ι → Set X := fun p => Classical.choose (hpair p.1 p.2)
  have hWopen : ∀ p, IsOpen (W p) := fun p => (Classical.choose_spec (hpair p.1 p.2)).1
  have hWmem : ∀ p, x₀ ∈ W p := fun p => (Classical.choose_spec (hpair p.1 p.2)).2.1
  have hWcomp : ∀ p x, x ∈ W p →
      (F x₀ p.1 ≤ F x₀ p.2 ↔ F x p.1 ≤ F x p.2) :=
    fun p => (Classical.choose_spec (hpair p.1 p.2)).2.2
  refine ⟨orderChamber F ∩ ⋂ p, W p,
    (isOpen_orderChamber F).inter (isOpen_iInter_of_finite hWopen),
    ⟨hx₀, Set.mem_iInter.mpr hWmem⟩, Set.inter_subset_left, ?_⟩
  intro x hx i j
  exact hWcomp (i, j) x (Set.mem_iInter.mp hx.2 (i, j))

end TDA.Filtration
