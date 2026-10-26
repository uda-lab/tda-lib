import TDA.Persistence.PrincipalDownsetRankResolution
import TDA.Persistence.FiniteRankProjectiveHomDimension

/-!
# Hom dimension of principal-downset injectives

A principal downset has Hom projective dimension at most one less than the
number of minimal complement generators, with natural subtraction giving degree
zero at top, where the downset is itself rank projective. The bound follows
from the actual resolution rows and implies high-degree term vanishing for every certified minimal resolution. This
formalizes the principal-downset case of BOOS, arXiv:2208.00300v3,
Proposition 5.14, using its Notation 5.2 complement generators.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.PrincipalDownsetRankDimension

open CategoryTheory CategoryTheory.Limits
open PrincipalDownsetRankResolution

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S] [OrderBot S] [OrderTop S]

/-- The actual principal-downset resolution bounds the Ext-based Hom projective dimension. -/
theorem hasProjectiveDimensionLE (p : S) :
    HasProjectiveDimensionLE
      ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := S)).obj
        (PrincipalDownsetInjective.module p)) (complementCard p - 1) := by
  have h := FiniteRankProjectiveHomDimension.hasProjectiveDimensionLT_length
    (resolution (k := k) p)
  rw [resolution_length] at h
  have he : max 1 (complementCard p) = (complementCard p - 1) + 1 := by omega
  rw [he] at h
  exact h

/-- Every certified minimal resolution vanishes above the principal-downset bound,
including its terminal zero padding. -/
theorem termAt_isZero (p : S)
    (R : MinimalFiniteRankProjectiveResolution
      (k := k) (M := PrincipalDownsetInjective.module p))
    (j : ℕ) (hj : complementCard p - 1 < j) : IsZero (R.termAt j) :=
  (FiniteRankProjectiveHomDimension.hasProjectiveDimensionLE_iff R _).mp
    (hasProjectiveDimensionLE p) j hj

end TDA.Persistence.PrincipalDownsetRankDimension
