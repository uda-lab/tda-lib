# Ordinary projective dimension on finite lattices

Let `k` be an arbitrary field and `S` a finite bounded lattice. Write
`D(S) = FiniteInjectiveRankDimension.maxComplementCard (S := S)`, the maximum
number of minimal elements outside a principal downset. The module
`TDA.Persistence.OrdinaryFiniteLatticeDimension` proves that every actual
pointwise finite-dimensional persistence functor `M : PModule k S` has ordinary
Ext-based projective dimension at most `D(S)`. The category is the persistence
functor category itself; the result is not an estimate for arbitrary modules
over the incidence algebra.

For `a ≤ b`, the existing principal-upset inclusion
`HookCokernel.inclusion` is identified with the singleton face map, whose
injectivity is already proved. Its actual cokernel is the finite hook, so the
resulting categorical short-exact row and projectivity of both principal
upsets give ordinary projective dimension at most one for each finite hook.
The infinite hooks are projective. The existing occurrence-indexed
classification of rank-projectives then gives the same bound for every
pointwise finite-dimensional rank-projective.

An actual finite rank-projective resolution with `m` middle terms gives the
loose ordinary bound `PD(M) ≤ m`: its pointwise exact rows become categorical
short-exact rows, each middle term has ordinary projective dimension at most
one, and induction proceeds from the terminal zero object. The stored count is
only a sufficient bound; it is neither a shortestness statement nor an upper
bound on every supplied resolution's raw length. Applying this result to the
existing principal-downset resolution gives `PD(I_p) ≤ complementCard(p)` for
`p ≠ ⊤`. At `⊤`, the existing isomorphism to a projective principal upset gives
the sharper degree-zero bound.

Every pointwise finite-dimensional ordinary injective embeds into the existing
finite occurrence-indexed biproduct of principal-downset injectives. Its actual
retraction and finite-biproduct closure give ordinary dimension at most `D(S)`.
To remove any bound on a caller's module, the proof first exposes the count of
one already constructed finite rank-projective resolution,
`3 * Fintype.card S + 2`, and obtains a temporary uniform bound for all such
modules. It then descends that bound one step at a time using the actual
injective-presentation row `M → I(M) → Q(M)`, with `I(M)` ordinary injective
and `Q(M)` pointwise finite-dimensional. The temporary bound is discharged in
the final theorem.

For an actual coordinate grid with nonempty factors, the existing minimal-
complement count yields ordinary projective dimension at most `n`; for the
actual interval-pair poset it yields at most `2n` when `n ≥ 1`. These are
representation-category bounds. The ordinary dimension of the Hom module used
in minimal relative rank-resolution comparisons is a different invariant, and
this theorem does not imply relative resolution-term vanishing. No arbitrary
incidence-module equivalence, numerical incidence-algebra bound, universal
`2n−2` relative estimate, or stability conclusion is included.

The proof is a bounded representation-category component of the arguments in
[BOOS24-v3](references.md#BOOS24-v3), including the ordinary-dimension step
around Theorem 5.16. It uses the library's actual hook, finite-resolution,
injective-presentation and dimension-shift constructions; it does not claim the
source's broader incidence-algebra conclusion.
