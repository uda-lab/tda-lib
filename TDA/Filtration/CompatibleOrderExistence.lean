import TDA.Filtration.CompatibleOrder
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

universe u v
namespace TDA.Filtration

variable {V : Type u} {α : Type v} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]

/-- A proof-local grade, face-cardinality, and arbitrary finite rank key. -/
private def rankKey (f : FilterFunction K α)
    (q : TDA.Simplicial.TotalFace K ≃
      Fin (Fintype.card (TDA.Simplicial.TotalFace K)))
    (s : TDA.Simplicial.TotalFace K) :
    Lex (α × Lex (ℕ × Fin (Fintype.card (TDA.Simplicial.TotalFace K)))) :=
  _root_.toLex (f.value s, _root_.toLex (s.val.card, q s))

private theorem rankKey_injective (f : FilterFunction K α)
    (q : TDA.Simplicial.TotalFace K ≃
      Fin (Fintype.card (TDA.Simplicial.TotalFace K))) :
    Function.Injective (rankKey f q) := by
  intro s t h
  apply q.injective
  have hq := congrArg
    (fun k : Lex (α × Lex (ℕ × Fin (Fintype.card (TDA.Simplicial.TotalFace K)))) =>
      ((_root_.ofLex ((_root_.ofLex k).2)).2)) h
  simpa [rankKey, _root_.ofLex_toLex] using hq

private structure SortedEnumeration (f : FilterFunction K α) where
  enum : Fin (Fintype.card (TDA.Simplicial.TotalFace K)) ≃
    TDA.Simplicial.TotalFace K
  rank : TDA.Simplicial.TotalFace K ≃
    Fin (Fintype.card (TDA.Simplicial.TotalFace K))
  key_strictMono : StrictMono (rankKey f rank ∘ enum)

private noncomputable def sortedEnumeration (f : FilterFunction K α) :
    SortedEnumeration f := by
  let q := Fintype.equivFin (TDA.Simplicial.TotalFace K)
  letI : LinearOrder (TDA.Simplicial.TotalFace K) :=
    LinearOrder.lift' (rankKey f q) (rankKey_injective f q)
  letI : PartialOrder (TDA.Simplicial.TotalFace K) :=
    (inferInstance : LinearOrder (TDA.Simplicial.TotalFace K)).toPartialOrder
  letI : Preorder (TDA.Simplicial.TotalFace K) :=
    (inferInstance : LinearOrder (TDA.Simplicial.TotalFace K)).toPreorder
  let e := Fintype.orderIsoFinOfCardEq
    (TDA.Simplicial.TotalFace K) rfl
  refine ⟨e.toEquiv, q, ?_⟩
  intro i j hij
  change rankKey f q (e i) < rankKey f q (e j)
  exact e.strictMono hij

/-- Every filter with finitely many faces admits a compatible enumeration. -/
theorem exists_compatibleOrder (f : FilterFunction K α) :
    Nonempty (CompatibleOrder f) := by
  let sorted := sortedEnumeration f
  refine ⟨⟨sorted.enum, ?_, ?_⟩⟩
  · intro i j hface
    have hkey : rankKey f sorted.rank (sorted.enum i) <
        rankKey f sorted.rank (sorted.enum j) := by
      apply Prod.Lex.toLex_lt_toLex.mpr
      have hgrade := f.mono hface.subset
      rcases lt_or_eq_of_le hgrade with hg | hg
      · exact Or.inl hg
      · right
        constructor
        · exact hg
        · apply Prod.Lex.toLex_lt_toLex.mpr
          exact Or.inl (Finset.card_lt_card hface)
    by_contra hnot
    have hji : j ≤ i := not_lt.mp hnot
    have hreverse := sorted.key_strictMono.monotone hji
    exact (not_le_of_gt hkey) hreverse
  · intro i j hij
    have hkey := sorted.key_strictMono.monotone hij
    change rankKey f sorted.rank (sorted.enum i) ≤
      rankKey f sorted.rank (sorted.enum j) at hkey
    exact Prod.Lex.monotone_fst _ _ hkey

/-- Grade monotonicity along an enumeration is equivalent to reflection of strict grade order. -/
theorem CompatibleOrder.monotone_enum_iff_reflects_lt
    (f : FilterFunction K α)
    (e : Fin (Fintype.card (TDA.Simplicial.TotalFace K)) ≃
      TDA.Simplicial.TotalFace K) :
    Monotone (f.value ∘ e) ↔
      ∀ i j, f.value (e i) < f.value (e j) → i < j := by
  constructor
  · intro h i j hij
    exact h.reflect_lt hij
  · intro h i j hij
    exact le_of_not_gt (fun hgrade => (not_lt_of_ge hij) (h j i hgrade))

#print axioms rankKey
#print axioms rankKey_injective
#print axioms SortedEnumeration
#print axioms SortedEnumeration.mk
#print axioms SortedEnumeration.enum
#print axioms SortedEnumeration.rank
#print axioms SortedEnumeration.key_strictMono
#print axioms sortedEnumeration
#print axioms exists_compatibleOrder
#print axioms CompatibleOrder.monotone_enum_iff_reflects_lt

end TDA.Filtration
