import TDA.Simplicial.FiniteComplex
import TDA.Filtration.FilterFunction
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Combinatorics.Colex

set_option autoImplicit false

/-!
# Canonical grade-compatible orders on finite face presentations

`CompatibleOrder` records a bijective enumeration of faces, with proper faces before
cofaces and nondecreasing filtration values. `CompatibleOrder.ofLex` constructs one for a
finite presentation by sorting the key `(grade, cardinality, colex)`. The finite presentation
provides the executable face data; the order on grades determines whether a particular value
function can be evaluated at runtime.
-/

universe u w

namespace TDA.Filtration

variable {V : Type u} {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}

/-- A bijective enumeration of faces that respects both face inclusion and grade. -/
structure CompatibleOrder [Fintype (TDA.Simplicial.TotalFace K)]
    (f : FilterFunction K α) where
  /-- Every face occurs exactly once, indexed by its finite cardinality. -/
  enum : Fin (Fintype.card (TDA.Simplicial.TotalFace K)) ≃
    TDA.Simplicial.TotalFace K
  /-- A proper face always occurs before its coface, including at tied grades. -/
  face_lt : ∀ i j, (enum i).val ⊂ (enum j).val → i < j
  /-- Filtration values are nondecreasing along the enumeration. -/
  monotone : Monotone (f.value ∘ enum)

namespace CompatibleOrder

variable {n : ℕ}

/-- The canonical key: grade first, then face cardinality, then finite-set colex. -/
def lexKey (C : TDA.Simplicial.FiniteComplex n)
    (f : FilterFunction C.toPre α)
    (s : TDA.Simplicial.TotalFace C.toPre) :
    Lex (α × Lex (ℕ × Colex (Finset (Fin n)))) :=
  _root_.toLex (f.value s, _root_.toLex (s.val.card, toColex s.val))

/-- The key distinguishes faces, even when grades and cardinalities tie. -/
theorem lexKey_injective (C : TDA.Simplicial.FiniteComplex n)
    (f : FilterFunction C.toPre α) :
    Function.Injective (lexKey C f) := by
  intro s t h
  apply Subtype.ext
  have hv := congrArg (fun k : Lex (α × Lex (ℕ × Colex (Finset (Fin n)))) =>
    ofColex ((_root_.ofLex ((_root_.ofLex k).2)).2)) h
  simpa [lexKey, _root_.ofLex_toLex, ofColex_toColex] using hv

/-- Finite sorted enumeration together with the key-order certificate used by the constructor. -/
private structure SortedEnumeration (C : TDA.Simplicial.FiniteComplex n)
    (f : FilterFunction C.toPre α) where
  enum : Fin (Fintype.card (TDA.Simplicial.TotalFace C.toPre)) ≃
    TDA.Simplicial.TotalFace C.toPre
  key_strictMono : StrictMono (lexKey C f ∘ enum)

/-- Build the finite order isomorphism under the key-induced order, locally. -/
private def sortedEnumeration (C : TDA.Simplicial.FiniteComplex n)
    (f : FilterFunction C.toPre α) : SortedEnumeration C f := by
  letI : LinearOrder (TDA.Simplicial.TotalFace C.toPre) :=
    LinearOrder.lift' (lexKey C f) (lexKey_injective C f)
  letI : PartialOrder (TDA.Simplicial.TotalFace C.toPre) :=
    (inferInstance : LinearOrder (TDA.Simplicial.TotalFace C.toPre)).toPartialOrder
  letI : Preorder (TDA.Simplicial.TotalFace C.toPre) :=
    (inferInstance : LinearOrder (TDA.Simplicial.TotalFace C.toPre)).toPreorder
  let e := Fintype.orderIsoFinOfCardEq
    (TDA.Simplicial.TotalFace C.toPre) rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  change lexKey C f (e i) < lexKey C f (e j)
  exact e.strictMono hij

/-- Sort the finite face type by its canonical key and certify the resulting order. -/
def ofLex (C : TDA.Simplicial.FiniteComplex n)
    (f : FilterFunction C.toPre α) : CompatibleOrder f := by
  let sorted := sortedEnumeration C f
  refine ⟨sorted.enum, ?_, ?_⟩
  · intro i j hface
    have hkey : lexKey C f (sorted.enum i) < lexKey C f (sorted.enum j) := by
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
    change lexKey C f (sorted.enum i) ≤ lexKey C f (sorted.enum j) at hkey
    exact Prod.Lex.monotone_fst _ _ hkey

/-- The canonical keys strictly increase along the constructed enumeration. -/
theorem ofLex_key_strictMono (C : TDA.Simplicial.FiniteComplex n)
    (f : FilterFunction C.toPre α) :
    StrictMono (lexKey C f ∘ (ofLex C f).enum) := by
  exact (sortedEnumeration C f).key_strictMono

#print axioms sortedEnumeration

end CompatibleOrder
end TDA.Filtration
