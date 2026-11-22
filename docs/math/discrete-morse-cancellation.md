# Unit cancellation of a filtered chain complex

`TDA.Persistence.Morse.UnitCancellation` (namespace `TDA.Persistence.Morse.Cancellation`)
removes one pair of basis generators from a finite based chain complex. The pair must have
coefficient one, and for the filtration statements its two generators must have equal grade.
The reduced differential and the maps of the contraction are computable entry formulas, and
the contraction identities are proved for them. This is the single reduction step of
Mischaikow–Nanda ([MN13](references.md#MN13)); the comparison is in
[comparison with MN13](#comparison-with-mn13). The fixtures are in
`TDA.Persistence.Morse.UnitCancellationExamples`.

## Based complexes and the column convention

The carrier is a finite index type `ι` (`[Fintype ι] [DecidableEq ι]`) of basis generators
and a matrix `D : Matrix ι ι k` over a commutative ring `k`. Column `c` is `d c`: the entry
`D r c` is the coefficient of `r` in `d c`, and the matrix product is composition. This is the
convention of the finite F₂ layer, `FiniteInput.boundary` and the reduction in
`TDA.Persistence.Reduction`.

`IsBasedDifferential degree D` for `degree : ι → ℕ` has two fields: `D * D = 0`, and
`D r c ≠ 0 → degree c = degree r + 1`. `IsFilteredDifferential degree grade D` adds, for
`grade : ι → ℤ`, that `D` is grade-nonincreasing: `GradeNonincreasing grade grade D`, which
says `D r c ≠ 0 → grade r ≤ grade c`. `GradeNonincreasing gr gc M` is defined for rectangular
matrices with a row grade `gr` and a column grade `gc`, and it is decidable for finite index
types with decidable entries (the instance `GradeNonincreasing.decidable`).

No ordering of `ι` and no triangularity is assumed. Generators of the same grade need not be
strictly triangular in any order, and the tie-order fixture below shows that the inherited
order need not be triangular after cancellation.

`isFilteredDifferential_boundary` proves that, for every valid finite input `xs`, the boundary
`FiniteInput.boundary xs` over `ZMod 2` is a filtered differential for `FiniteInput.degree xs`
and the list grades `fun i => (xs.get i).2`.

## The reduction step

`IsUnitPair D a b` is `a ≠ b` together with `D a b = 1`: `a` is a face of `b` with
coefficient one. The survivors are the subtype `PairSurvivor a b` of generators other than
`a` and `b`, with the inherited degree `degree ∘ Subtype.val` and grade
`grade ∘ Subtype.val`. Survivors keep their original IDs as `Subtype.val`; nothing is
renumbered, and `card_pairSurvivor` counts `card ι - 2` of them when `a ≠ b`.

With the matrices

- the homotopy `homotopy a b`, written `H`, with `H a = b` and zero on every other generator;
- the survivor projection `survivorProjection a b`, written `Q`, restricting coordinates;
- the survivor inclusion `survivorInclusion a b`, written `J`,

the three maps of the reduction are defined entrywise:

- `reducedDifferential D a b r s = D r s - D r b * D a s`, written `d'`;
- `projection D a b s x`, written `p`, is `1` at `x = s`, `-(D s b)` at `x = a` and `0`
  otherwise, so `p s = s`, `p a = -Q (d b)` and `p b = 0`;
- `inclusion D a b x s`, written `i`, is `1` at `x = s`, `-(D a s)` at `x = b` and `0`
  otherwise, so `i s = s - D a s · b`.

The product forms are theorems, valid for every matrix `D` and every `a`, `b`:
`reducedDifferential_eq` is `d' = Q (D - D H D) J`, `projection_eq` is `p = Q (1 - D H)` and
`inclusion_eq` is `i = (1 - H D) J`. `reducedDifferential_eq_projection_mul_inclusion` proves
`d' = p D i` for a unit pair; its proof uses `D a b = 1`, through `H D H = H`.

## Contraction identities

For a unit pair `IsUnitPair D a b` of a matrix with `D * D = 0`:

- `reducedDifferential_sq_zero`: `d' * d' = 0`;
- `projection_mul`: `p D = d' p`, so `p` is a chain map;
- `mul_inclusion`: `D i = i d'`, so `i` is a chain map;
- `one_sub_inclusion_mul_projection`: `1 - i p = D H + H D`.

The entry `(b, a)` of the last identity reduces, by `(D * D) a b = 0`, to `D a a + D b b` on
both sides, so no separate assumption `D a a = D b b = 0` is needed. The following need only
`a ≠ b`, with no condition on `D`:

- `projection_mul_inclusion`: `p i = 1`;
- `homotopy_mul_homotopy`: `H H = 0`;
- `projection_mul_homotopy`: `p H = 0`;
- `homotopy_mul_inclusion`: `H i = 0`.

Under `D * D = 0` and `IsUnitPair D a b`, these eight identities make `(p, i, H)` a strong
deformation retraction of `D` onto `d'`, with the sign convention `1 - i p = D H + H D`.

For a based differential (`IsBasedDifferential degree D`) and a unit pair, the four maps
respect degrees on their supports. `reducedDifferential_lowersDegree` lowers the inherited
degree by one, `projection_degree` and `inclusion_degree` preserve degree, and
`homotopy_degree` raises it by one. `isBasedDifferential_reduced` concludes that `d'` is a
based differential for `degree ∘ Subtype.val`. No `[Nontrivial k]` is assumed: over the
trivial ring, every support hypothesis `entry ≠ 0` is false, and the four support statements
hold vacuously.

## Filtration

The four grade theorems assume only that `D` is grade-nonincreasing and that
`grade a = grade b`; they use neither `D * D = 0` nor `D a b = 1`:

- `reducedDifferential_gradeNonincreasing`: `d'` is grade-nonincreasing for the inherited
  grade;
- `projection_gradeNonincreasing` and `inclusion_gradeNonincreasing`: so are `p` and `i`,
  between the grade of `ι` and the inherited grade;
- `homotopy_gradeNonincreasing`: so is `H`, which needs only `grade a = grade b`.

`isFilteredDifferential_reduced` combines these with the degree results: for a filtered
differential, a unit pair and equal grades, `d'` is a filtered differential for the inherited
degree and grade.

`SublevelSupported g t x` says that a coordinate vector `x` vanishes on generators of grade
above `t`. `GradeNonincreasing.mulVec_sublevelSupported` proves that a grade-nonincreasing
matrix maps such vectors to such vectors, and `GradeNonincreasing.mul` proves that
grade-nonincreasing matrices compose. With the four theorems above, `d'`, `p`, `i` and `H`
therefore map the grade-`≤ t` coordinate subspace into the grade-`≤ t` subspace for every
`t`. So the contraction identities restrict to each grade sublevel. These restricted
identities are not stated as separate theorems, and nothing is claimed for arbitrary
tie-refined prefixes of a same-grade order.

## Fixtures

All fixtures are over `ZMod 2`. Every closed computation is a kernel `decide`.

The filled triangle `triangle` has positions 0 to 6 for A, B, C, AB, BC, CA, ABC. A, B, C and
AB have grade 0, BC and CA grade 1, and ABC grade 2. `triangle_boundary` proves that its
finite-input boundary is the written-out matrix `tD`, and `triangle_isFilteredDifferential`
follows from `isFilteredDifferential_boundary`. The pair (B, AB) is a unit pair of equal grade
0 (`triangle_isUnitPair`, `triangle_grade_eq`). Cancelling it gives:

- `triangle_reduced_BC`: `d' BC = A + C`, where `d BC = B + C`;
- `triangle_correction`: `D A BC = 0` but the coefficient of A in `d' BC` is 1, so it
  comes entirely from the correction term `-(D A AB · D B BC)`, which is 1 over `ZMod 2`;
- `triangle_reduced_ABC`: `d' ABC = BC + CA`, unchanged, since `D B ABC = 0`;
- `triangle_reduced`: the whole reduced differential `tReduced`, with
  `d' BC = d' CA = A + C` and `d' ABC = BC + CA`.

`triangle_not_free` records `D B BC = 1`. So B is also a face of BC, which enters at grade 1,
and B is not a free face of AB at the final level; no free-face hypothesis is used.

The pure unit pair `uD` on `Fin 2` is the two-cell complex `d b = a`, which is not
simplicial. With both generators at grade 0, it is a filtered differential, no generator
survives (`unit_survivor_card`), and `unit_contraction` evaluates `1 = D H + H D`, so `H` is a
contracting homotopy of the whole complex.

The same `uD` with `a` at grade 0 and `b` at grade 1 (`vGrade`) is still a filtered
differential with `D a b = 1` (`unequal_isFilteredDifferential`). Here the general formulas
still give an unfiltered contraction, but:

- `unequal_homotopy_not_filtered`: `H a = b` raises grade;
- `unequal_no_filtered_contraction`: no grade-nonincreasing matrix `H` satisfies
  `1 - i p = D H + H D` for any `p` and `i` through the empty survivor type. Since `i p = 0`,
  the entry `(a, a)` would force `1 = H b a`, and grade-nonincreasingness forces `H b a = 0`.

The reason is the barcode. In the sublevel at grade 0 only `a` is present, a degree-0 cycle
that is not a boundary. At grade 1 it is the boundary of `b`, so the barcode has the bar
`[0, 1)` between the two grades. A filtered contraction onto the survivor complex would
restrict to every sublevel. The survivor complex is empty, so the grade-0 sublevel would be
contractible, contradicting the bar. This explanation is not a Lean theorem: the library
states no homology or barcode of these complexes. For an unequal-grade pair in a larger
complex, `p`, `i` and `d'` can also raise grade, and no general impossibility theorem is
claimed beyond this fixture.

The tie-order fixture `wD` on `Fin 4` has all generators at grade 0, in the order
`a < s < r < b` (positions 0 to 3), with `a`, `r` in degree 0, `s`, `b` in degree 1,
`d s = a` and `d b = a + r`. Cancelling (a, b) gives the single entry `d' s = r`
(`tie_reduced`). `tie_not_triangular` records that this entry is new and that `s` precedes
`r`. A valid cancellation therefore does not preserve triangularity in the inherited order.
This is the regression data for a later reducer adapter (#1061); this unit sorts nothing.

## Comparison with MN13

MN13 define the reduction step in the outline of the proof of Thm. 2.4 (pp. 335–336), for a
complex with an acyclic matching over a principal ideal domain. Their incidence `κ(η, ξ)` is
the coefficient of `ξ` in `∂η` (Def. 2.1), so `κ(η, ξ) = D ξ η` here, with `Q = a` and
`w(Q) = b`.

| MN13 | Lean |
|---|---|
| `X_Q = X \ {Q, w(Q)}` | `PairSurvivor a b` |
| `κ_Q`, eq. (8) | `reducedDifferential` |
| `ψ_Q`, eq. (9) | `projection` |
| `φ_Q`, eq. (10) | `inclusion` |
| `Θ` in the proof of Lemma 2.5 | `homotopy` |
| `ψ_Q ∘ φ_Q = id` | `projection_mul_inclusion` |
| `Θ∂ + ∂Θ = I − φ_Q ∘ ψ_Q` | `one_sub_inclusion_mul_projection` |

The comparison mode is specialization in the unit: MN divide by the unit `κ(w(Q), Q)`, and
here it is specialised to `D a b = 1`. No rescaling by a general unit is provided. MN leave the
chain-map property of `ψ_Q` and `φ_Q` to the reader; here it is `projection_mul` and
`mul_inclusion`. The coefficient setting is an extension: the Lean statements need neither an
acyclic matching nor a principal ideal domain, and they hold over any commutative ring.

The filtration statements specialise the filtration argument of the proof of Prop. 4.4
(pp. 340–341) to one pair, with an integer grade in place of MN's frame index `b`. MN show
that the reduction maps are the identity on the lower frames; the Lean statements show that
all four maps are grade-nonincreasing. MN's Def. 4.1, which keeps each matched pair within
one frame, is background for the equal-grade hypothesis.

`isFilteredDifferential_boundary`, `GradeNonincreasing.mul`, the annihilation identities and
the unequal-grade fixture are library derivations attributed to no numbered result. See the
[MN13 source mapping](references.md#MN13).

## What is not provided

- No iteration of cancellations, pair schedule, admissible-pivot invariant, composition of
  contractions, Morse complex, homology or persistence isomorphism; these are #1041.
- No reducer adapter, reindexing of survivors to `Fin`, or grading-compatible ordering; these
  are #1061.
- No matching check or search, no bridge to Mathlib `HomologicalComplex` or `Homotopy`, and
  no runtime bound or speedup claim.
