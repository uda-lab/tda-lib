import TDA.Filtration.FilterFunction

set_option autoImplicit false

/-!
# Face-value sublevel regression fixtures

Small private examples exercise empty domains, weak threshold inequalities, ties, absent ambient
vertices, and the distinction between the original complex and the ambient top complex.
-/

universe u w

namespace TDA.Filtration.Examples

/-- No face or grade value is selected for an empty domain. -/
private def emptyFilter (V : Type u) (α : Type w) [LinearOrder α] :
    FilterFunction (⊥ : PreAbstractSimplicialComplex V) α where
  value := fun s => ((mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro τ σ _
    exact ((mem_bot_iff τ.val).mp τ.property).elim

private theorem empty_generic (V : Type u) (α : Type w) [LinearOrder α] (r : α) :
    (emptyFilter V α).sublevel r = ⊥ :=
  FilterFunction.sublevel_bot _ r

private theorem empty_vempty (r : ℤ) :
    (emptyFilter Empty ℤ).sublevel r = ⊥ :=
  FilterFunction.sublevel_bot _ r

private def singletonFilter (V : Type u) (x : V) :
    FilterFunction (singletonFace x) ℤ where
  value := fun _ => 3
  mono := by intros; exact le_refl 3

private theorem singleton_low (V : Type u) (x : V) :
    (singletonFilter V x).sublevel 2 = ⊥ := by
  apply FilterFunction.sublevel_eq_bot_of_forall_lt
  intro s
  norm_num [singletonFilter]

private theorem singleton_at (V : Type u) (x : V) :
    (singletonFilter V x).sublevel 3 = singletonFace x := by
  apply FilterFunction.sublevel_eq_self_of_forall_le
  intro s
  norm_num [singletonFilter]

private theorem singleton_support_low (V : Type u) (x : V) :
    support (singletonFilter V x).sublevelFiltration 2 = ∅ := by
  apply support_eq_empty_of_eq_bot
  exact singleton_low V x

private theorem singleton_support_at (V : Type u) (x : V) :
    support (singletonFilter V x).sublevelFiltration 3 = {x} := by
  ext y
  change ({y} : Finset V) ∈ (singletonFilter V x).sublevel 3 ↔ y ∈ ({x} : Set V)
  rw [singleton_at]
  simp [mem_singletonFace_iff]

/-- Equal values preserve the simultaneous entry of both vertices and their edge. -/
private def tiedFilter : FilterFunction (⊤ : PreAbstractSimplicialComplex (Fin 2)) ℤ where
  value := fun _ => 5
  mono := by intros; exact le_refl 5

private theorem tied_low : tiedFilter.sublevel 4 = ⊥ := by
  apply FilterFunction.sublevel_eq_bot_of_forall_lt
  intro s
  norm_num [tiedFilter]

private theorem tied_at :
    tiedFilter.sublevel 5 = (⊤ : PreAbstractSimplicialComplex (Fin 2)) := by
  apply FilterFunction.sublevel_eq_self_of_forall_le
  intro s
  norm_num [tiedFilter]

private theorem tied_faces :
    ({0} : Finset (Fin 2)) ∈ tiedFilter.sublevel 5 ∧
    ({1} : Finset (Fin 2)) ∈ tiedFilter.sublevel 5 ∧
    ({0, 1} : Finset (Fin 2)) ∈ tiedFilter.sublevel 5 := by
  rw [tied_at]
  constructor
  · change ({0} : Finset (Fin 2)).Nonempty
    simp
  constructor
  · change ({1} : Finset (Fin 2)).Nonempty
    simp
  · change ({0, 1} : Finset (Fin 2)).Nonempty
    simp

/-- A sublevel of the singleton on `0` does not acquire the ambient vertex `1`. -/
private def oneVertexFilter :
    FilterFunction (singletonFace (0 : Fin 2)) ℤ where
  value := fun _ => 0
  mono := by intros; exact le_refl 0

private theorem oneVertex_at :
    oneVertexFilter.sublevel 0 = singletonFace (0 : Fin 2) := by
  apply FilterFunction.sublevel_eq_self_of_forall_le
  intro s
  norm_num [oneVertexFilter]

private theorem oneVertex_missing :
    ({1} : Finset (Fin 2)) ∉ oneVertexFilter.sublevel 0 := by
  rw [oneVertex_at]
  exact (mem_singletonFace_iff 0 {1}).not.mpr (by decide)

private theorem oneVertex_support :
    support oneVertexFilter.sublevelFiltration 0 = ({0} : Set (Fin 2)) := by
  ext x
  change ({x} : Finset (Fin 2)) ∈ oneVertexFilter.sublevel 0 ↔
    x ∈ ({0} : Set (Fin 2))
  rw [oneVertex_at]
  simp [mem_singletonFace_iff]

private theorem oneVertex_not_top :
    oneVertexFilter.sublevel 0 ≠ (⊤ : PreAbstractSimplicialComplex (Fin 2)) := by
  intro h
  have h1 : ({1} : Finset (Fin 2)) ∈ oneVertexFilter.sublevel 0 := by
    rw [h]
    change ({1} : Finset (Fin 2)).Nonempty
    simp
  exact oneVertex_missing h1

-- Generic interface checks: these types require no order, finiteness, or decidable equality on V.
example {V : Type u} {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V} (f : FilterFunction K α) (_r : α) :
    SimplicialFiltration α V := f.sublevelFiltration

example {V : Type u} {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V} (f : FilterFunction K α) (r : α)
    (v : V) : v ∈ support f.sublevelFiltration r ↔
      ∃ hs : ({v} : Finset V) ∈ K, f.value ⟨{v}, hs⟩ ≤ r :=
  f.mem_support_sublevelFiltration_iff r v

end TDA.Filtration.Examples
