import TDA.Persistence.Reduction.FiniteInputActiveBasis

/-! Executable coordinate matrices, matching original birth indices across queries. -/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.FiniteInput

/-- Target rows and source columns match the same original birth face.
Its homological interpretation requires valid input and `a ≤ b`. -/
def basisTransition (xs : Input) (p : ℕ) (a b : ℤ) :
    Matrix (BasisIndex xs p b) (BasisIndex xs p a) (ZMod 2) :=
  fun j i => if (basisRecord xs p b j).birthIndex = (basisRecord xs p a i).birthIndex
    then 1 else 0

theorem basisTransition_apply (xs : Input) (p : ℕ) (a b : ℤ)
    (j : BasisIndex xs p b) (i : BasisIndex xs p a) :
    basisTransition xs p a b j i =
      if (basisRecord xs p b j).birthIndex = (basisRecord xs p a i).birthIndex
        then 1 else 0 := rfl

theorem basisTransition_self (xs : Input) (p : ℕ) (a : ℤ) :
    basisTransition xs p a a = 1 := by
  ext j i
  simp only [basisTransition_apply, (basisRecord_birth_injective xs p a).eq_iff,
    Matrix.one_apply]

end TDA.Persistence.Reduction.FiniteInput
