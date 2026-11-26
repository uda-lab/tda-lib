import TDA.Persistence.TotalPersistence
import TDA.Persistence.DiagramRegularity

/-!
# Regularity of total persistence as a diagram loss

On an ordered presentation, degree-`p` total persistence with `p ≠ 0` is the sum of the
`p`-th powers of the absolute endpoint differences of all finite pairs: a diagonal pair, which
`orderedQ` deletes, contributes zero. For an even exponent the absolute value disappears and
the sum is a polynomial in the coordinates, so total persistence is `Cʳ` through every ordered
presentation of every diagram, for every `r`. This supplies the loss hypothesis of the
first- and second-order calculus of sublevel diagrams.

These are elementary library results, not attributed to a source.
-/

set_option autoImplicit false

namespace TDA.Persistence

open scoped ContDiff

private theorem sum_filter_offDiagonal_eq (f : ℝ × ℝ → ℝ)
    (hf : ∀ q, q.1 = q.2 → f q = 0) (l : List (ℝ × ℝ)) :
    ((l.filter fun q => q.1 ≠ q.2).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
    by_cases hq : q.1 = q.2
    · simpa [hq, hf q hq] using ih
    · simpa [hq] using congrArg (fun a : ℝ => f q + a) ih

/-- Total persistence of an ordered presentation, for a nonzero exponent: the sum over all
finite pairs, diagonal pairs included. -/
theorem totalPersistence_orderedQ {p : ℕ} (hp : p ≠ 0) (m n : ℕ)
    (z : DiagramCoordinates m n) :
    (orderedQ m n z).totalPersistence p = ∑ i : Fin m, |(z.1 i).2 - (z.1 i).1| ^ p := by
  classical
  have h := sum_filter_offDiagonal_eq (fun q : ℝ × ℝ => |q.2 - q.1| ^ p)
    (by intro q hq; simp [hq, hp]) (List.ofFn z.1)
  rw [Diagram.totalPersistence, finitePart_orderedQ]
  simpa [List.sum_ofFn, Function.comp_def] using h

/-- For an even positive exponent, total persistence is `Cʳ` through every ordered
presentation of every diagram. -/
theorem totalPersistence_crThroughAllRepresentatives {p : ℕ} (hp : Even p) (hp0 : p ≠ 0)
    (r : ℕ∞ω) (D : Diagram ℝ) :
    CrThroughAllRepresentatives r (Diagram.totalPersistence p) D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, ?_⟩
  apply contDiffOn_univ.mpr
  have hs : ContDiff ℝ r (fun w : DiagramCoordinates m n =>
      ∑ i : Fin m, ((w.1 i).2 - (w.1 i).1) ^ p) := by
    apply ContDiff.sum
    intro i _
    fun_prop
  have he : Diagram.totalPersistence p ∘ orderedQ m n =
      fun w : DiagramCoordinates m n => ∑ i : Fin m, ((w.1 i).2 - (w.1 i).1) ^ p := by
    funext w
    rw [Function.comp_apply, totalPersistence_orderedQ hp0]
    exact Finset.sum_congr rfl fun i _ => hp.pow_abs _
  rw [he]
  exact hs

/-- The `C¹` form, the loss hypothesis of the first-order calculus. -/
theorem totalPersistence_c1ThroughAllRepresentatives {p : ℕ} (hp : Even p) (hp0 : p ≠ 0)
    (D : Diagram ℝ) : C1ThroughAllRepresentatives (Diagram.totalPersistence p) D :=
  CrThroughAllRepresentatives.one_iff.mp (totalPersistence_crThroughAllRepresentatives hp hp0 1 D)

/-- The `C²` form, the loss hypothesis of the second-order calculus. -/
theorem totalPersistence_c2ThroughAllRepresentatives {p : ℕ} (hp : Even p) (hp0 : p ≠ 0)
    (D : Diagram ℝ) : C2ThroughAllRepresentatives (Diagram.totalPersistence p) D :=
  CrThroughAllRepresentatives.two_iff.mp (totalPersistence_crThroughAllRepresentatives hp hp0 2 D)

end TDA.Persistence
