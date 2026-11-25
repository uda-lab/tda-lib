import Mathlib.Data.List.Pi
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Exact bottleneck computation for integer presentations

The finite search retains original list positions, including repeated values. Its
costs are doubled natural numbers; essential-count mismatch gives infinity.
-/

namespace TDA.Persistence.IntegerBottleneck

/-- An ordered integer presentation. Equal finite endpoints are ignored. -/
structure Presentation where
  finite : List (ℤ × ℤ)
  essential : List ℤ
  deriving DecidableEq, Repr

/-- Retained finite occurrences carry their position in the original input. -/
abbrev FiniteIndex (D : Presentation) :=
  {i : Fin D.finite.length // (D.finite.get i).1 ≠ (D.finite.get i).2}

/-- Essential occurrences also retain repeated births as distinct positions. -/
abbrev EssentialIndex (D : Presentation) := Fin D.essential.length

/-- Enumerate retained original positions, without comparing real numbers. -/
def finiteIndices (D : Presentation) : List (FiniteIndex D) :=
  (List.finRange D.finite.length).filterMap fun i =>
    if h : (D.finite.get i).1 ≠ (D.finite.get i).2 then some ⟨i, h⟩ else none

@[simp] theorem mem_finiteIndices (D : Presentation) (i : FiniteIndex D) :
    i ∈ finiteIndices D := by
  simp only [finiteIndices, List.mem_filterMap]
  exact ⟨i.1, List.mem_finRange _, by rw [dite_eq_left i.2]⟩

private def maps {A B : Type} [DecidableEq A]
    (as : List A) (bs : List B) (ha : ∀ a, a ∈ as) : List (A → B) :=
  (as.pi fun _ => bs).map fun f a => f a (ha a)

private theorem mem_maps {A B : Type} [DecidableEq A]
    (as : List A) (bs : List B) (ha : ∀ a, a ∈ as)
    (f : A → B) (hf : ∀ a, f a ∈ bs) : f ∈ maps as bs ha := by
  apply List.mem_map.mpr
  refine ⟨fun a _ => f a, (List.mem_pi _ _).mpr (fun a _ => hf a), rfl⟩

/-- Raw candidate data; validity is checked by finite integer-index quantifiers. -/
abbrev Assignment (D E : Presentation) :=
  (FiniteIndex D → Option (FiniteIndex E)) × (EssentialIndex D → EssentialIndex E)

/-- Finite occurrences are partially injective and essential occurrences bijective. -/
def Valid {D E : Presentation} (a : Assignment D E) : Prop :=
  (∀ i i' j, a.1 i = some j → a.1 i' = some j → i = i') ∧
    Function.Bijective a.2

instance {D E : Presentation} (a : Assignment D E) : Decidable (Valid a) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

/-- Valid matching data. The proof only certifies the executable validity test. -/
abbrev Candidate (D E : Presentation) := {a : Assignment D E // Valid a}

/-- The finite partial assignment uses original input positions. -/
def Candidate.finiteMap {D E : Presentation} (a : Candidate D E) :
    FiniteIndex D → Option (FiniteIndex E) := a.1.1

/-- The essential assignment uses original essential-list positions. -/
def Candidate.essentialMap {D E : Presentation} (a : Candidate D E) :
    EssentialIndex D → EssentialIndex E := a.1.2

theorem Candidate.finiteMap_injective {D E : Presentation} (a : Candidate D E)
    (i i' : FiniteIndex D) (j : FiniteIndex E)
    (h : a.finiteMap i = some j) (h' : a.finiteMap i' = some j) : i = i' :=
  a.2.1 i i' j h h'

theorem Candidate.essentialMap_bijective {D E : Presentation} (a : Candidate D E) :
    Function.Bijective a.essentialMap := a.2.2

/-- Matched finite positions, exported as ordinary zero-based natural pairs. -/
def Candidate.finitePairs {D E : Presentation} (a : Candidate D E) : List (ℕ × ℕ) :=
  (finiteIndices D).filterMap fun i => (a.finiteMap i).map fun j => (i.1.val, j.1.val)

/-- Matched essential positions, exported as ordinary zero-based natural pairs. -/
def Candidate.essentialPairs {D E : Presentation} (a : Candidate D E) : List (ℕ × ℕ) :=
  List.ofFn fun i => (i.val, (a.essentialMap i).val)

/-- Enumerate all finite assignments and all essential functions, then filter.
For `m,n` retained finite indices and `e,f` essential indices this inspects
`(n+1)^m * f^e` raw candidates, rather than enumerating permutations directly. The count is
documented, not proved. -/
def candidates (D E : Presentation) : List (Candidate D E) :=
  let fs := maps (finiteIndices D) (none :: (finiteIndices E).map some)
    (mem_finiteIndices D)
  let es := maps (List.finRange D.essential.length) (List.finRange E.essential.length)
    (fun _ => List.mem_finRange _)
  (fs.product es).filterMap fun a => if h : Valid a then some ⟨a, h⟩ else none

/-- The explicit search represents every valid assignment. -/
theorem mem_candidates (D E : Presentation) (a : Candidate D E) :
    a ∈ candidates D E := by
  apply List.mem_filterMap.mpr
  refine ⟨a.1, List.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · apply mem_maps
    intro i
    cases h : a.1.1 i with
    | none => simp
    | some j => simp [mem_finiteIndices]
  · exact mem_maps _ _ _ _ (fun _ => List.mem_finRange _)
  · simp [a.2]

/-- Twice the diagonal cost, using the magnitude of an integer difference. -/
def diagonalTwice (p : ℤ × ℤ) : ℕ := (p.2 - p.1).natAbs

/-- Twice the maximum-norm finite-pair cost. -/
def finiteTwice (p q : ℤ × ℤ) : ℕ :=
  2 * max (p.1 - q.1).natAbs (p.2 - q.2).natAbs

/-- Twice the essential-birth cost. -/
def essentialTwice (b c : ℤ) : ℕ := 2 * (b - c).natAbs

/-- The exact doubled maximum cost, including unmatched targets as well as sources. -/
def twiceCost {D E : Presentation} (a : Candidate D E) : ℕ :=
  max ((Finset.univ : Finset (FiniteIndex D)).sup fun i =>
      match a.1.1 i with
      | none => diagonalTwice (D.finite.get i.1)
      | some j => finiteTwice (D.finite.get i.1) (E.finite.get j.1))
    (max ((Finset.univ : Finset (FiniteIndex E)).sup fun j =>
      if ∃ i, a.1.1 i = some j then 0 else diagonalTwice (E.finite.get j.1))
      ((Finset.univ : Finset (EssentialIndex D)).sup fun i =>
        essentialTwice (D.essential.get i) (E.essential.get (a.1.2 i))))

/-- Exhaustively choose a minimum-cost candidate. Ties are deterministic. -/
def solve (D E : Presentation) : Option (Candidate D E) :=
  if D.essential.length = E.essential.length then
    (candidates D E).argmin twiceCost
  else none

/-- The doubled distance; infinity has no matching attached. -/
def twiceDistance (D E : Presentation) : WithTop ℕ :=
  match solve D E with
  | none => ⊤
  | some a => (twiceCost a : WithTop ℕ)

/-- Executable output: an exact doubled distance and optional occurrence data. -/
structure Result (D E : Presentation) where
  twiceDistance : WithTop ℕ
  matching : Option (Candidate D E)

/-- Compute the doubled value and its finite optimal occurrence witness together. -/
def run (D E : Presentation) : Result D E :=
  let matching := solve D E
  ⟨match matching with
    | none => ⊤
    | some a => (twiceCost a : WithTop ℕ), matching⟩

@[simp] theorem run_twiceDistance (D E : Presentation) :
    (run D E).twiceDistance = twiceDistance D E := rfl

@[simp] theorem run_matching (D E : Presentation) : (run D E).matching = solve D E := rfl

/-- The selected candidate has no larger executed cost than any valid assignment. -/
theorem solve_minimal (D E : Presentation) {a : Candidate D E}
    (h : solve D E = some a) (b : Candidate D E) : twiceCost a ≤ twiceCost b := by
  unfold solve at h
  split at h
  · exact List.le_of_mem_argmin (mem_candidates D E b) h
  · contradiction

/-- Equal essential counts give the explicit all-deleted finite assignment and
the order-preserving essential bijection. -/
def deleteFinite (D E : Presentation) (h : D.essential.length = E.essential.length) :
    Candidate D E :=
  ⟨(fun _ => none, finCongr h), by
    constructor
    · simp
    · exact (finCongr h).bijective⟩

/-- A valid assignment exists exactly when the essential counts agree. -/
theorem candidate_nonempty_iff (D E : Presentation) :
    Nonempty (Candidate D E) ↔ D.essential.length = E.essential.length := by
  constructor
  · rintro ⟨a⟩
    simpa only [EssentialIndex, Fintype.card_fin] using
      Fintype.card_congr (Equiv.ofBijective a.1.2 a.2.2)
  · intro h
    exact ⟨deleteFinite D E h⟩

/-- No matching is returned exactly when the essential counts disagree. -/
theorem solve_eq_none_iff (D E : Presentation) :
    solve D E = none ↔ D.essential.length ≠ E.essential.length := by
  constructor
  · intro hs he
    have hm := mem_candidates D E (deleteFinite D E he)
    have hs' : (candidates D E).argmin twiceCost = none := by simpa [solve, he] using hs
    have hn : candidates D E = [] := List.argmin_eq_none.mp hs'
    rw [hn] at hm
    exact List.not_mem_nil hm
  · intro hn
    simp [solve, hn]

/-- The doubled output is infinite exactly when essential counts disagree. -/
theorem twiceDistance_eq_top_iff (D E : Presentation) :
    twiceDistance D E = ⊤ ↔ D.essential.length ≠ E.essential.length := by
  rw [← solve_eq_none_iff D E]
  cases h : solve D E <;> simp [twiceDistance, h]

/-- Every equal-count input returns a finite witness, including empty inputs. -/
theorem solve_exists_iff (D E : Presentation) :
    (∃ a, solve D E = some a) ↔ D.essential.length = E.essential.length := by
  constructor
  · rintro ⟨a, ha⟩
    by_contra hn
    have h := (solve_eq_none_iff D E).mpr hn
    simp [h] at ha
  · intro he
    cases h : solve D E with
    | none => exact False.elim (((solve_eq_none_iff D E).mp h) he)
    | some a => exact ⟨a, rfl⟩

end TDA.Persistence.IntegerBottleneck
