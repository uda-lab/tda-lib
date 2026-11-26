import TDA.Simplicial.H0Augmentation

set_option autoImplicit false

/-!
# Underlying finsets of deleted faces

`deletedFace` and `SimplexAttachment.oldDeletedFace` are defined through the increasing
enumeration `Finset.orderEmbOfFin`, which `decide` does not evaluate. This module states
their underlying finsets, the case of an edge `{a, b}` with `a < b`, and forms of the
separated-vertices theorems of `TDA.Simplicial.H0Augmentation` that take the vertices of the
edge directly.
-/

namespace TDA.Simplicial

variable {V : Type*} [LinearOrder V]

/-- The enumeration of the pair `{a, b}` with `a < b` has `a` at position `0`. -/
theorem orderEmbOfFin_pair_zero {a b : V} (hab : a < b)
    (h : ({a, b} : Finset V).card = 0 + 1 + 1) :
    ({a, b} : Finset V).orderEmbOfFin h 0 = a := by
  have hf : (![a, b] : Fin 2 → V) = ({a, b} : Finset V).orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique h (f := ![a, b])
      (fun x => by fin_cases x <;> simp)
      (by
        intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all)
  exact (congrFun hf 0).symm

/-- The enumeration of the pair `{a, b}` with `a < b` has `b` at position `1`. -/
theorem orderEmbOfFin_pair_one {a b : V} (hab : a < b)
    (h : ({a, b} : Finset V).card = 0 + 1 + 1) :
    ({a, b} : Finset V).orderEmbOfFin h 1 = b := by
  have hf : (![a, b] : Fin 2 → V) = ({a, b} : Finset V).orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique h (f := ![a, b])
      (fun x => by fin_cases x <;> simp)
      (by
        intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all)
  exact (congrFun hf 1).symm

variable {K : PreAbstractSimplicialComplex V}

/-- The underlying finset of a deleted face omits the vertex at the deleted position. -/
theorem deletedFace_val (n : ℕ) (s : Face K (n + 1)) (i : Fin (n + 2)) :
    (deletedFace K n s i).val = s.val.erase (s.val.orderEmbOfFin s.2.2 i) :=
  rfl

/-- Deleting position `0` of an edge `{a, b}` with `a < b` leaves `{b}`. -/
theorem deletedFace_val_pair_zero (s : Face K 1) {a b : V} (hab : a < b)
    (hs : s.val = {a, b}) : (deletedFace K 0 s 0).val = {b} := by
  rw [deletedFace_val]
  obtain ⟨s, hsK, hc⟩ := s
  change s = {a, b} at hs
  subst hs
  rw [orderEmbOfFin_pair_zero hab hc]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, rfl | rfl⟩
    · exact (hx rfl).elim
    · rfl
  · rintro rfl
    exact ⟨hab.ne', Or.inr rfl⟩

/-- Deleting position `1` of an edge `{a, b}` with `a < b` leaves `{a}`. -/
theorem deletedFace_val_pair_one (s : Face K 1) {a b : V} (hab : a < b)
    (hs : s.val = {a, b}) : (deletedFace K 0 s 1).val = {a} := by
  rw [deletedFace_val]
  obtain ⟨s, hsK, hc⟩ := s
  change s = {a, b} at hs
  subst hs
  rw [orderEmbOfFin_pair_one hab hc]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, rfl | rfl⟩
    · rfl
    · exact (hx rfl).elim
  · rintro rfl
    exact ⟨hab.ne, Or.inl rfl⟩

namespace SimplexAttachment

variable {L : PreAbstractSimplicialComplex V} {p : ℕ} (A : SimplexAttachment K L (p + 1))

/-- The underlying finset of an old deleted face omits the vertex at the deleted position of
the attached simplex. -/
theorem oldDeletedFace_val (i : Fin (p + 2)) :
    (A.oldDeletedFace i).val =
      A.simplex.erase (A.simplex.orderEmbOfFin A.card_simplex i) :=
  rfl

/-- For an attached edge `{a, b}` with `a < b`, the old deleted face at position `0` is `{b}`. -/
theorem oldDeletedFace_val_pair_zero (A : SimplexAttachment K L 1) {a b : V} (hab : a < b)
    (hA : A.simplex = {a, b}) : (A.oldDeletedFace 0).val = {b} :=
  deletedFace_val_pair_zero A.newFace hab hA

/-- For an attached edge `{a, b}` with `a < b`, the old deleted face at position `1` is `{a}`. -/
theorem oldDeletedFace_val_pair_one (A : SimplexAttachment K L 1) {a b : V} (hab : a < b)
    (hA : A.simplex = {a, b}) : (A.oldDeletedFace 1).val = {a} :=
  deletedFace_val_pair_one A.newFace hab hA

end SimplexAttachment

/-- A vertex predicate constant along every edge takes the same value on both deleted faces of
an edge, as a predicate on the vertices of a face. -/
theorem forall_mem_deletedFace_zero_iff_one (Q : V → Prop)
    (hQ : ∀ σ : Face K 1, ∀ u ∈ σ.val, ∀ v ∈ σ.val, Q u ↔ Q v) (σ : Face K 1) :
    (∀ v ∈ (deletedFace K 0 σ 0).val, Q v) ↔ ∀ v ∈ (deletedFace K 0 σ 1).val, Q v := by
  have key : ∀ i : Fin 2, ∃ x ∈ σ.val, (deletedFace K 0 σ i).val = {x} := by
    intro i
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (deletedFace K 0 σ i).2.2
    refine ⟨x, ?_, hx⟩
    have : x ∈ (deletedFace K 0 σ i).val := by rw [hx]; exact Finset.mem_singleton_self x
    exact Finset.mem_of_mem_erase this
  obtain ⟨x, hx, hx'⟩ := key 0
  obtain ⟨y, hy, hy'⟩ := key 1
  rw [hx', hy']
  simp only [Finset.mem_singleton, forall_eq]
  exact hQ σ x hx y hy

namespace SimplexAttachment

/-- An edge attached between two vertices that a vertex predicate constant along the edges of
the old complex separates gives a nonzero attaching class. -/
theorem attachingHomologyClass_ne_zero_of_separated_edge {L : PreAbstractSimplicialComplex V}
    (k : Type*) [Field k] (A : SimplexAttachment K L 1) (Q : V → Prop)
    (hQ : ∀ σ : Face K 1, ∀ u ∈ σ.val, ∀ v ∈ σ.val, Q u ↔ Q v)
    {a b : V} (hab : a < b) (hA : A.simplex = {a, b}) (ha : ¬ Q a) (hb : Q b) :
    A.attachingHomologyClass k ≠ 0 := by
  classical
  refine SimplexAttachment.attachingHomologyClass_ne_zero_of_separated_vertices K k A
    (fun τ => ∀ v ∈ τ.val, Q v) (forall_mem_deletedFace_zero_iff_one Q hQ) ?_ ?_
  · rw [A.oldDeletedFace_val_pair_zero hab hA]
    simpa using hb
  · rw [A.oldDeletedFace_val_pair_one hab hA]
    simpa using ha

end SimplexAttachment

/-- Two vertices that a vertex predicate constant along the edges of the target complex
separates stay independent under the degree-zero quotient inclusion. -/
theorem quotientIncl_injective_of_separated_vertices (k : Type*) [Field k]
    {L : PreAbstractSimplicialComplex V} (h : K ≤ L) (u v : Face K 0)
    (hdecomp : ∀ c : Chain K k 0, c = Finsupp.single u (c u) + Finsupp.single v (c v))
    (Q : V → Prop) (hQ : ∀ σ : Face L 1, ∀ x ∈ σ.val, ∀ y ∈ σ.val, Q x ↔ Q y)
    (hu : ∀ w ∈ u.val, Q w) (hv : ∃ w ∈ v.val, ¬ Q w) :
    Function.Injective (simplicialQuotientIncl k h 0) := by
  classical
  refine quotientIncl_injective_of_two_vertices_separated K k h u v hdecomp
    (fun τ => ∀ w ∈ τ.val, Q w) (forall_mem_deletedFace_zero_iff_one Q hQ) hu ?_
  intro hv'
  obtain ⟨w, hw, hQw⟩ := hv
  exact hQw (hv' w hw)

end TDA.Simplicial
