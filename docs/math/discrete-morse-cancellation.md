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
deformation retraction of `D` onto `d'`, with the sign convention `1 - i p = D H + H D`;
`FilteredContraction.ofUnitPair` bundles them as a `FilteredContraction`.

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
states no homology value or barcode of these complexes. For an unequal-grade pair in a larger
complex, `p`, `i` and `d'` can also raise grade, and no general impossibility theorem is
claimed beyond this fixture.

The tie-order fixture `wD` on `Fin 4` has all generators at grade 0, in the order
`a < s < r < b` (positions 0 to 3), with `a`, `r` in degree 0, `s`, `b` in degree 1,
`d s = a` and `d b = a + r`. Cancelling (a, b) gives the single entry `d' s = r`
(`tie_reduced`). `tie_not_triangular` records that this entry is new and that `s` precedes
`r`. A valid cancellation therefore does not preserve triangularity in the inherited order.
Fixture R1 of
[the reducer order of a filtered based complex](#the-reducer-order-of-a-filtered-based-complex)
sorts the survivors into the order `r, s`, in which `d'` is strictly upper triangular;
`TDA.Persistence.Morse.UnitCancellation` itself sorts nothing.

## Filtered contractions and their composition

`TDA.Persistence.Morse.FilteredContraction` (namespace `TDA.Persistence.Morse.Cancellation`)
bundles the maps of a contraction as data, so that contractions can be composed and
transported. For finite carriers `ι` and `κ` with decidable equality and a commutative ring
`k`, a
`FilteredContraction degree grade D degree' grade' D'` of the based complex
`(ι, degree, grade, D)` onto `(κ, degree', grade', D')` is a structure with three matrices,
`proj : Matrix κ ι k`, `incl : Matrix ι κ k` and `htpy : Matrix ι ι k`, written `p`, `i` and
`h`, and thirteen Prop fields:

- the chain-map equations `proj_mul` (`p D = D' p`) and `mul_incl` (`D i = i D'`);
- `proj_mul_incl` (`p i = 1`) and `one_sub_incl_mul_proj` (`1 - i p = D h + h D`), with the
  sign convention of `one_sub_inclusion_mul_projection`;
- the side conditions `htpy_mul_htpy` (`h h = 0`), `proj_mul_htpy` (`p h = 0`) and
  `htpy_mul_incl` (`h i = 0`);
- degree support: `proj_degree` and `incl_degree` say that `p` and `i` preserve degree on
  their supports, and `htpy_degree` that `h x y ≠ 0` implies `degree x = degree y + 1`;
- grade bounds: `proj_grade`, `incl_grade` and `htpy_grade` say that all three matrices are
  `GradeNonincreasing`.

The differentials `D` and `D'`, the degrees and the grades are parameters, not fields. So
`trans` typechecks only when the middle complex of the two contractions agrees, and
`ofUnitPair` names its target exactly. `D * D = 0` and the filtration of `D` are not fields
either: they enter only as hypotheses of `ofUnitPair` and of the three `*_target` theorems
below, and `refl`, `copy`, `trans` and `reindex` need no hypothesis beyond their inputs. The
Prop fields are proof-irrelevant, so two contractions with the same matrices are
interchangeable for every statement about the matrices.

`refl degree grade D` is the identity contraction, with `p = i = 1` and `h = 0`.
`c₁.trans c₂` composes a contraction of the large complex onto a middle one with a contraction
of the middle complex onto a small one, in diagrammatic order; the three carriers may be
different types. Its projection is `p₂ p₁`, its inclusion `i₁ i₂` and its homotopy
`h = h₁ + i₁ h₂ p₁`. The chain-map equations and `p i = 1` compose directly. For the rest:

- `h h = h₁ h₁ + h₁ i₁ h₂ p₁ + i₁ h₂ p₁ h₁ + i₁ h₂ (p₁ i₁) h₂ p₁`. The first three terms
  vanish by `h₁ h₁ = 0`, `h₁ i₁ = 0` and `p₁ h₁ = 0`, and the last is `i₁ h₂ h₂ p₁ = 0`;
- `p h = p₂ p₁ h₁ + p₂ (p₁ i₁) h₂ p₁ = p₂ h₂ p₁ = 0`;
- `h i = h₁ i₁ i₂ + i₁ h₂ (p₁ i₁) i₂ = i₁ h₂ i₂ = 0`;
- `1 - i₁ i₂ p₂ p₁ = (1 - i₁ p₁) + i₁ (1 - i₂ p₂) p₁ = D h₁ + h₁ D + i₁ (D' h₂ + h₂ D') p₁`,
  and `i₁ D' = D i₁` and `D' p₁ = p₁ D` turn the last term into
  `D (i₁ h₂ p₁) + (i₁ h₂ p₁) D`.

The degree fields of the composite follow from those of the factors on the supports of the
products, and the grade fields from `GradeNonincreasing.mul` and the new
`GradeNonincreasing.add`. `trans_proj`, `trans_incl` and `trans_htpy` state the three matrices
of the composite by `rfl`, as `refl_*`, `copy_*`, `reindex_*` and `ofUnitPair_*` do for the
other constructions.

`c.reindex e` transports the small complex along `e : κ ≃ μ`: the target becomes
`(degree' ∘ e.symm, grade' ∘ e.symm, D'.submatrix e.symm e.symm)`, the projection
`proj.submatrix e.symm id`, the inclusion `incl.submatrix id e.symm`, and the homotopy is
unchanged. Only the small side is transported. `c.copy hdeg hgr hD` keeps the three matrices
and rewrites the small complex's degree, grade and differential along equalities. Together they
move a contraction onto nested survivor subtypes to a flat carrier, such as a subtype of the
original positions, and restate it there with the flat degree, grade and differential without
casts; fixture G2 below does this once.

`ofUnitPair hD hp hg` packages the single cancellation of the earlier sections: for
`hD : IsFilteredDifferential degree grade D`, a unit pair `hp : IsUnitPair D a b` and
`hg : grade a = grade b`, it is the contraction onto
`(degree ∘ Subtype.val, grade ∘ Subtype.val, reducedDifferential D a b)` with matrices
`projection D a b`, `inclusion D a b` and `homotopy a b`, whose fields are the theorems of the
earlier sections.

For every filtered contraction `c`:

- `differential_eq`: `D' = p D i`;
- `sq_zero_target`: `D * D = 0` implies `D' * D' = 0`, since
  `p D i p D i = p (D D) i - p D (1 - i p) D i = -p D (D h + h D) D i = 0`;
- `isBasedDifferential_target` and `isFilteredDifferential_target`: if `D` is a based,
  respectively filtered, differential, so is `D'`;
- `proj_mulVec_incl_mulVec`: `p (i y) = y`;
- `sub_incl_mulVec_proj_mulVec`: `x - i (p x) = D (h x) + h (D x)`.

Sublevel restriction is not restated. Each of `p`, `i` and `h` is grade-nonincreasing, so by
`GradeNonincreasing.mulVec_sublevelSupported` each maps vectors supported in grades `≤ t` to
such vectors. If `D` is also grade-nonincreasing, as under
`IsFilteredDifferential degree grade D` (and then `D'` is too, by
`isFilteredDifferential_target`), the identities above restrict to each grade sublevel. These
restricted identities are not stated as separate theorems. The section
[sublevel homology and the induced isomorphism](#sublevel-homology-and-the-induced-isomorphism)
states the support facts that homology needs, such as `htpy_mem_sublevelChains`; those need no
hypothesis on `D`.

The fixtures are in `TDA.Persistence.Morse.FilteredContractionExamples`, over `ZMod 2`, with
every closed computation a kernel `decide`. They reuse the filled triangle `tD` with the grade
`cGrade`: A, B, C, AB and BC at grade 0, CA at grade 1 and ABC at grade 2. The regrading is
needed: with the list grades of `triangle`, no equal-grade unit pair remains after cancelling
(B, AB), since every remaining incidence joins a grade-0 vertex to a grade-1 edge or a grade-1
edge to the grade-2 face.

- G1. `step1` cancels (B, AB) by `ofUnitPair`. `step2` cancels (C, BC) on the survivors
  `PairSurvivor tB tAB`, from `isFilteredDifferential_reduced`, with pivot `d' BC` having
  coefficient 1 on C; its survivors form the nested subtype `TS2`. The composite
  `twoStep = step1.trans step2` has the single differential entry `d'' ABC = CA`
  (`twoStep_differential`). Its projection sends A, B, C to A, CA to CA, ABC to ABC and AB, BC
  to 0 (`twoStep_proj`); its inclusion sends A to A, CA to AB + BC + CA and ABC to ABC
  (`twoStep_incl`); its homotopy sends B to AB, C to AB + BC and every other generator to 0
  (`twoStep_htpy`). The homotopy on C comes entirely from the correction term `i₁ h₂ p₁`:
  `p₁ C = C`, `h₂ C = BC` and `i₁ BC = AB + BC`, while `h₁ C = 0`. The lift AB + BC + CA of
  the critical edge is the boundary cycle of the triangle. `twoStep_values_homotopy` checks
  `1 - i p = D h + h D` on the written-out matrices directly, independently of the general
  proof.
- G2. `critEquiv : TS2 ≃ Crit` identifies the nested survivors with the flat subtype `Crit` of
  the positions A, CA and ABC, keeping the original IDs, and
  `critContraction = twoStep.reindex critEquiv`. `crit_differential` (`d ABC = CA` on `Crit`),
  `crit_proj`, `crit_incl` and `crit_htpy` state the values of G1 with the small side on
  `Crit`, and `crit_grade` states that the transported grades are the grades `cGrade` of the
  original positions.
  `critFlat` restates `critContraction` by `copy` with the flat degree `tDegree ∘ Subtype.val`,
  grade `cGrade ∘ Subtype.val` and differential `critD`, and `critFlat_proj` and
  `critFlat_incl` evaluate it.

G2 is the contraction part of the transport the #1065 forward note asked for, on one
instance; `submatrix` lemmas for `reducedDifferential`, `projection` and `inclusion` are not
provided. No general equivalence from nested survivor subtypes to a Finset of critical cells
is provided either; the schedule recursion of
[iterated cancellation along a pivot schedule](#iterated-cancellation-along-a-pivot-schedule)
avoids nested survivors by running each step on a Finset-indexed carrier.
`TDA.Persistence.Morse.FilteredContraction` formalises no homology; the section
[sublevel homology and the induced isomorphism](#sublevel-homology-and-the-induced-isomorphism)
adds it in a separate module.

## Iterated cancellation along a pivot schedule

`TDA.Persistence.Morse.IteratedCancellation` (namespace `TDA.Persistence.Morse.Cancellation`)
cancels a list of unit pairs one after the other and composes the single cancellations of
`ofUnitPair` into one filtered contraction onto the generators that are not cancelled. The
schedule is supplied; this module does not derive it from a matching.

### Schedules and the pivot invariant

A schedule is a list `l : List (ι × ι)` of (lower, upper) pairs of generators of a based
complex `(ι, degree, grade, D)`, in the column convention of
[based complexes and the column convention](#based-complexes-and-the-column-convention):
`D r c` is the coefficient of `r` in `d c`. `scheduleEndpoints l` lists the `2·|l|` endpoints
in order; its body is that of `MatchingInput.endpoints`. `IsPivotSchedule grade D l` is the
conjunction of three conditions:

- the endpoints are distinct (`(scheduleEndpoints l).Nodup`);
- every pair `(a, b)` of `l` has `D a b = 1` and `grade a = grade b`;
- `l.Pairwise fun p q => D p.1 q.2 = 0`: the lower generator of a pair is never a face of the
  upper generator of a later pair.

The instance `IsPivotSchedule.decidable` decides it when equality of generators and of
coefficients is decidable. `isPivotSchedule_iff_get` restates the third condition in indexed
form: write `(a i, b i)` for the pairs in schedule order; then `D (a i) (b j) ≠ 0` with
`i ≠ j` forces `j < i`. So the matched block, with rows `a i` and columns `b j`, is unit lower
triangular in schedule order.

The direction is the one that a topological rank of a matching provides. In
`MatchingInput.arrow`, an unmatched cover points from coface to face, a matched pair from face
to coface, and `IsTopologicalRank` asks the rank to increase strictly along every arrow. For
`FiniteInput.boundary`, suppose `D (a i) (b j) ≠ 0` with `i ≠ j`. If `a i` is a codimension-one
face of `b j`, the cover `(a i, b j)` is not a matched pair, since the endpoints are distinct,
so the arrows `a j → b j → a i` give `rank (a j) < rank (a i)`. Listing the pairs in increasing
rank of the lower face therefore gives the third condition of `IsPivotSchedule`; the distinct
endpoints, the unit coefficients and the equal grades have to come from the certified pairs.
This derivation is not formalized in `TDA.Persistence.Morse.IteratedCancellation`;
`TDA.Persistence.Morse.MatchingSchedule` proves it (`isCover_of_boundary_ne_zero`,
`rank_lt_of_boundary_ne_zero`, `isPivotSchedule_schedule`), see
[the pivot schedule of a certified matching](#the-pivot-schedule-of-a-certified-matching).
Here the order is supplied, and fixture H1 in
[schedule fixtures](#schedule-fixtures) checks one such order on the square.

### One cancellation step

`cancelStep D a b r s = D r s - D r b * D a s` is the entry formula of
`reducedDifferential D a b`, on all of `ι` rather than on the survivors.
`scheduleMatrix l D` applies it along `l`, head first:
`scheduleMatrix ((a, b) :: l) D = scheduleMatrix l (cancelStep D a b)`.

- `cancelStep_apply_of_eq_zero`: a column `s` with `D a s = 0` is unchanged.
- `IsPivotSchedule.cancelStep_apply_snd`: in a pivot schedule `p :: l`, the head condition of
  `Pairwise` gives `D p.1 q.2 = 0` for every `q ∈ l`, so the column of every upper generator
  of `l` is unchanged, on every row.
- `IsPivotSchedule.cancelStep`: the tail `l` is a pivot schedule for `cancelStep D p.1 p.2`.
- `IsPivotSchedule.head_not_mem`: the two generators of the head pair are distinct and are not
  endpoints of the tail.
- `IsPivotSchedule.isUnitPair_reducedDifferential`: every later pair is an `IsUnitPair` of
  `reducedDifferential D a b` on the survivors `PairSurvivor a b`.

The proof of `IsPivotSchedule.cancelStep` is short. For pairs `q` and `q'` of the tail, the
entries `D q.1 q.2 = 1` and, for `q` before `q'`, `D q.1 q'.2 = 0` lie in the columns `q.2` and
`q'.2`, which `cancelStep_apply_snd` leaves unchanged. The endpoints of the tail are a part of
the distinct endpoints of `p :: l`, and the grade condition does not involve `D`.

The recursion cancels the head of the schedule. With the invariant, the head's lower generator
is a face of no later upper generator, so cancelling it leaves every later upper column
unchanged, and this is the whole proof above. The following remarks are argued by hand only
and are not formalized:

- In a unit lower triangular matched block, cancelling any pair `k` changes the entry at
  `(a i, b j)` by `−D (a i) (b k) * D (a k) (b j)`, which can be nonzero only for `j < k < i`.
  So the diagonal stays 1 and triangularity persists, whichever pair is cancelled next.
- The transposed condition `l.Pairwise fun p q => D q.1 p.2 = 0` is also preserved head first,
  because cancelling the head leaves the rows of all later lower generators unchanged.

The invariant is sufficient for the recursion, not necessary: fixture G1 of
[filtered contractions and their composition](#filtered-contractions-and-their-composition)
cancels (B, AB) and then (C, BC), and fixture H2 in [schedule fixtures](#schedule-fixtures)
checks that this order is not a pivot schedule. The module keeps the single direction that a
rank of the lower face provides. Fixture N there records cyclic pairs none of whose six
orders is a pivot schedule.

### Critical generators and the composed contraction

`scheduleSurvivors l S` removes the endpoints of `l` from a Finset `S` pair by pair, by the
same recursion as `scheduleMatrix`; `mem_scheduleSurvivors` states that its members are the
elements of `S` that are not endpoints. `criticalSet l = scheduleSurvivors l Finset.univ`, so
`x ∈ criticalSet l ↔ x ∉ scheduleEndpoints l` (`mem_criticalSet`). `Critical l` is the
subtype `{x : ι // x ∈ criticalSet l}`, so the critical generators keep their original IDs as
`Subtype.val`, and `card_critical` gives `Fintype.card (Critical l) = Fintype.card ι - 2·|l|`
for distinct endpoints. `criticalDifferential D l` is `scheduleMatrix l D` restricted to
`Critical l`. It takes no hypothesis, so it can be evaluated without building the
contraction.

For `hD : IsFilteredDifferential degree grade D` and `hl : IsPivotSchedule grade D l`,
`FilteredContraction.ofSchedule hD hl` is a filtered contraction of `(ι, degree, grade, D)`
onto `(Critical l, degree ∘ Subtype.val, grade ∘ Subtype.val, criticalDifferential D l)`. The
target is named exactly, on the flat carrier `Critical l`. It is built in four layers:

- `survivorEquiv ha hb` is the concrete equivalence from `PairSurvivor ⟨a, ha⟩ ⟨b, hb⟩`, the
  survivors inside the carrier `{x // x ∈ S}`, to `{x // x ∈ (S.erase a).erase b}`; both
  directions keep `x.val`.
- `cancelOn` is `ofUnitPair` on `{x // x ∈ S}`, transported by `reindex` along
  `survivorEquiv` and restated by `copy rfl rfl rfl` with the flat degree and grade and the
  differential `(cancelStep M a b).submatrix Subtype.val Subtype.val`.
- `ofScheduleOn l S M` composes these steps with `trans`. Its hypotheses are that `M`
  restricted to `S` is a filtered differential, that `l` is a pivot schedule for `M`, and that
  every endpoint of `l` lies in `S`. After the head step, the filtered differential property
  comes from `isFilteredDifferential_target` and the pivot invariant from
  `IsPivotSchedule.cancelStep`.
- `toUniv` restates the original complex on `{x // x ∈ Finset.univ}` by `refl`, `reindex` and
  `copy`, and `ofSchedule` is `toUniv` followed by `ofScheduleOn l Finset.univ D`.

No cast is needed. After `reindex`, the transported degree is
`((degree ∘ val) ∘ val) ∘ e.symm`, which is definitionally `degree ∘ val` because `e` is the
concretely defined `survivorEquiv`, so `rfl` closes all three `copy` equalities. Because
`scheduleSurvivors` and `scheduleMatrix` follow the recursion of `ofScheduleOn`, the carrier
and the differential reached after each step are, definitionally, those the next step starts
from. All data are computable, and the recursion is structural on `l`, so no data body matches
on a proof.

The characterizing facts are:

- `criticalDifferential_eq`: `criticalDifferential D l = proj * D * incl`, from
  `differential_eq`;
- `isFilteredDifferential_criticalDifferential`: `criticalDifferential D l` is a filtered
  differential for the inherited degree and grade, from `isFilteredDifferential_target`, so it
  squares to zero, lowers degree by one and does not increase grade;
- `ofSchedule_congr`: the projection, inclusion and homotopy of `ofSchedule` depend on `D`
  only through its value. The fixtures use it to move between `FiniteInput.boundary` and a
  written-out matrix.

Sublevel restriction is not restated; it is `GradeNonincreasing.mulVec_sublevelSupported`
applied to the grade fields of the contraction. The isomorphism `sublevelHomologyIso` of
[sublevel homology and the induced isomorphism](#sublevel-homology-and-the-induced-isomorphism)
applies to every filtered contraction, so also to `ofSchedule`, but this module states no
instance of it.

### What is not proved

`TDA.Persistence.Morse.IteratedCancellation` provides none of the following:

- an explicit formula for the reduced differential, the projection, the inclusion or the
  homotopy, such as a sum over gradient paths; the matrices are defined only by the recursion;
- independence of the result from the schedule order; fixture H2 checks agreement with G1 in
  one instance only;
- preservation of the invariant when a pair other than the head is cancelled;
- any derivation of a schedule from an acyclic matching or a #1039 `CertifiedMatching`;
  `TDA.Persistence.Morse.MatchingSchedule` derives one from a certified matching, a pivot
  schedule for `FiniteInput.boundary` on a valid input, see
  [the pivot schedule of a certified matching](#the-pivot-schedule-of-a-certified-matching);
- any homology or persistence statement; the simplicial bridge and the main theorem of #1041
  are in
  [the simplicial bridge and the Morse persistence theorem](#the-simplicial-bridge-and-the-morse-persistence-theorem).

### Schedule fixtures

The fixtures are in `TDA.Persistence.Morse.IteratedCancellationExamples`, over `ZMod 2`. Every
closed computation is checked by `decide +kernel`; the index bounds of the position names
`qA` … `qACD` and `oA` … `oAC` use a plain `decide`, and `square_isFilteredDifferential` and
`sqD_isFilteredDifferential` are term proofs from `isFilteredDifferential_boundary` and
`square_boundary`. `square_boundary` and `circle_boundary` first unfold the boundary with
`norm_num`, as `triangle_boundary` of `TDA.Persistence.Morse.UnitCancellationExamples` does,
because `FiniteInput.boundary` does not reduce in the kernel.

- H1. The square `square` of `TDA.Persistence.Morse.FiniteInputMatchingExamples`, with A, B,
  C, D, AB, BC and CD at grade 0, AD at grade 1 and AC, ABC and ACD at grade 2, on
  `FiniteInput.boundary square`. `sqSchedule` is (AC, ABC), (D, CD), (C, BC), (B, AB): the
  pairs of `squarePairs` (`sqSchedule_perm`) in increasing rank of the lower face, which is 2,
  4, 6 and 8 for the rank of `square_check`. It is a pivot schedule
  (`sqSchedule_isPivotSchedule`); the list order of `squarePairs` is not, since B is a face of
  BC (`squarePairs_not_isPivotSchedule`). The critical set is {A, AD, ACD}
  (`sq_criticalSet`), and the reduced differential has the single entry `d ACD = AD`
  (`sq_criticalDifferential`). The projection sends A, B, C and D to A, AD to AD, ACD to ACD
  and every other generator to 0 (`sq_proj`); the inclusion sends A to A, AD to
  AB + BC + CD + AD and ACD to ABC + ACD (`sq_incl`); the homotopy sends B to AB, C to
  AB + BC, D to AB + BC + CD, AC to ABC and every other generator to 0 (`sq_htpy`). As a hand
  check of the chain-map equation on ACD: `D (i ACD) = ∂ABC + ∂ACD = AB + BC + CD + AD`, which
  is `i (d ACD)`.
- H2. The filled triangle `tD` with the grade `cGrade` of the G1 and G2 fixtures (A, B, C, AB and
  BC at grade 0, CA at 1, ABC at 2). `triSchedule` is (C, BC), (B, AB), and it is a pivot
  schedule (`triSchedule_isPivotSchedule`); G1's order (B, AB), (C, BC) is not, since B is a
  face of BC (`g1Order_not_isPivotSchedule`). The critical set is G2's `critSet`
  (`tri_mem_criticalSet`), and the reduced differential, the projection and the inclusion are
  G2's `critD`, `critProj` and `critIncl`, read through `toCrit`
  (`tri_criticalDifferential`, `tri_proj`, `tri_incl`); the homotopy is G1's `twoStepHtpy`
  (`tri_htpy`). The same values as G1 and G2 arise here from the opposite order of the same
  two pairs; this is one instance, not a theorem about order independence.
- N. The hollow triangle `circle` of `TDA.Persistence.Morse.FiniteInputMatchingExamples`, with
  A, B, C, AB, BC and AC all at grade 0, and the cyclic pairs (A, AB), (B, BC), (C, AC) of
  `cyclicPairs`, for which the checker of #1039 accepts no rank (`cyclic_no_certificate`).
  `cyclicOrders` lists six distinct permutations of `cyclicPairs` (`cyclicOrders_perm`), and
  none of them is a pivot schedule (`cyclic_not_isPivotSchedule`). `D C AC = 1`, but after
  cancelling (A, AB) and then (B, BC) head first, the entry at (C, AC) is 0
  (`cyclic_pivot_destroyed`), so the third pair can no longer be cancelled.

## Sublevel homology and the induced isomorphism

`TDA.Persistence.Morse.FilteredHomology` (namespace `TDA.Persistence.Morse.Cancellation`)
forms the homology of every grade sublevel of a based complex, packages it as a persistence
module over `ℤ`, and proves that a filtered contraction induces an isomorphism of these
persistence modules. The submodules have Prop-valued carriers, and the maps, the persistence
module and the isomorphisms are `noncomputable` definitions; this module computes no homology
by evaluation.

For a finite carrier `ι`, `degree : ι → ℕ`, `grade : ι → ℤ` and `D : Matrix ι ι k` over a
commutative ring `k`, in the column convention above:

- `DegreeSupported degree p x` says that `x` vanishes on every generator whose degree is not
  `p`;
- `sublevelChains degree grade p t` is the submodule of vectors `x : ι → k` with
  `DegreeSupported degree p x` and `SublevelSupported grade t x`;
- `sublevelCycles degree grade D p t` is its intersection with the kernel of `D`, so its
  members are the sublevel chains with `D.mulVec x = 0` (`mem_sublevelCycles`);
- `sublevelBoundaries degree grade D p t` is the image under `D` of
  `sublevelChains degree grade (p + 1) t` (`mem_sublevelBoundaries`): the boundaries of
  degree-`p + 1` chains in grades `≤ t`;
- `sublevelHomology degree grade D p t` is
  `cycles ⧸ boundaries.comap cycles.subtype`, the cycles modulo the boundaries that lie among
  them.

No hypothesis on `D` enters these definitions. `sublevelBoundaries_le_sublevelCycles` proves
that, for `IsFilteredDifferential degree grade D`, every sublevel boundary is a sublevel cycle;
its proof uses all three parts of the hypothesis: the degree condition for degree `p`, the
grade bound for grades `≤ t`, and `D * D = 0` for `D (D y) = 0`. For such a `D`, the submodule
divided out is therefore all of `sublevelBoundaries`, viewed inside the cycles, and
`sublevelHomology` is the usual degree-`p` homology of the subcomplex spanned by the
generators of grade `≤ t`.

Chains, cycles and boundaries grow with the grade (`sublevelChains_mono`,
`sublevelCycles_mono`, `sublevelBoundaries_mono`). For `h : t ≤ t'`,
`sublevelHomologyMap degree grade D p h` is the linear map induced by the inclusion of cycles;
`sublevelHomologyMap_mk` states that it sends the class of a cycle to the class of the same
vector, and `sublevelHomologyMap_id` and `sublevelHomologyMap_comp` state identity and
composition. `sublevelHomologyPModule degree grade D p` is a `PModule.{v, 0, max u v} k ℤ` for
`ι : Type u` and `k : Type v`, with value `ModuleCat.of k (sublevelHomology degree grade D p t)`
at `t` (`sublevelHomologyPModule_obj`) and structure maps `sublevelHomologyMap`
(`structureMapLinear_sublevelHomologyPModule`). It is defined for every matrix `D`.

Let `c : FilteredContraction degree grade D degree' grade' D'`. The declarations about `c`
take both carriers in one universe, `ι κ : Type u`, so that the two persistence modules are
objects of the same functor category.

- `proj_mem_sublevelChains` and `incl_mem_sublevelChains`: `proj` and `incl` map degree-`p`
  chains in grades `≤ t` of one complex to degree-`p` chains in grades `≤ t` of the other, by
  the degree fields `proj_degree`, `incl_degree` and the grade fields `proj_grade`,
  `incl_grade`.
- `htpy_mem_sublevelChains`: `htpy` maps degree-`p` chains in grades `≤ t` to degree-`p + 1`
  chains in grades `≤ t`, by `htpy_degree` and `htpy_grade`.
- `proj_mulVec_mul` and `incl_mulVec_mul` are the vector forms of the chain-map equations, and
  with them `proj` and `incl` map sublevel cycles to sublevel cycles and sublevel boundaries to
  sublevel boundaries (`proj_mem_sublevelCycles`, `incl_mem_sublevelCycles`,
  `proj_mem_sublevelBoundaries`, `incl_mem_sublevelBoundaries`).
- `c.homologyProj p t` and `c.homologyIncl p t` are the induced linear maps of sublevel
  homology, with `homologyProj_mk` and `homologyIncl_mk` on represented classes.

The two maps are mutually inverse. For a sublevel cycle `y` of the small complex,
`proj (incl y) = y` by `proj_mulVec_incl_mulVec`, so `homologyProj` undoes `homologyIncl` on
representatives. For a sublevel cycle `x` of the large complex, `sub_incl_mulVec_proj_mulVec`
gives `x - incl (proj x) = D (htpy x) + htpy (D x)`, and `D x = 0` leaves
`x - incl (proj x) = D (htpy x)`. Since `htpy x` is a degree-`p + 1` chain in grades `≤ t`,
the difference is a sublevel boundary (`sub_incl_proj_mem_sublevelBoundaries`), so `x` and
`incl (proj x)` have the same class. `c.sublevelHomologyEquiv p t` is the resulting
`LinearEquiv`, with forward map `homologyProj` and inverse `homologyIncl`
(`sublevelHomologyEquiv_apply`, `sublevelHomologyEquiv_symm_apply`).

`homologyProj_comp_sublevelHomologyMap` is naturality in the grade: for `t ≤ t'`, both
composites send the class of a cycle `x` at grade `t` to the class of `proj x` at grade `t'`.
`c.sublevelHomologyIso p` is the isomorphism
`sublevelHomologyPModule degree grade D p ≅ sublevelHomologyPModule degree' grade' D' p` in the
functor category, built with `NatIso.ofComponents` from the components
`(c.sublevelHomologyEquiv p t).toModuleIso`. It runs from the large complex to the small one;
`sublevelHomologyIso_hom_app` and `sublevelHomologyIso_inv_app` identify its components with
`homologyProj` and `homologyIncl`. `c.finrank_sublevelHomology_eq p t` states that the two
sublevel homologies have equal `Module.finrank` at every degree and grade.

None of these results about `c` has `D * D = 0`, `IsBasedDifferential` or
`IsFilteredDifferential` as a hypothesis. Their proofs use the degree and grade fields of `c`,
the chain-map fields `proj_mul` and `mul_incl`, and `proj_mul_incl` and
`one_sub_incl_mul_proj` through the two vector identities; no proof in the module refers to
the side conditions `htpy * htpy = 0`, `proj * htpy = 0` and `htpy * incl = 0`.

The fixtures are in `TDA.Persistence.Morse.FilteredHomologyExamples`, over `ZMod 2`. They
reuse the triangle `tD`, the grade `cGrade` and the contraction `critFlat` onto the critical
complex `critD` on `Crit` from the fixtures above. On `Crit`,
`critDegree` and `critGrade` are the inherited degree and grade: A in degree 0 at grade 0, CA
in degree 1 at grade 1 and ABC in degree 2 at grade 2, with the single differential entry
`d ABC = CA`.

- H1. The critical complex, computed directly. `H₀` has dimension 1 for `t ≥ 0`
  (`crit_finrank_zero`) and 0 for `t < 0` (`crit_finrank_zero_of_lt`). `H₁` has dimension 0
  for `t < 1` (`crit_finrank_one_of_lt`), 1 at `t = 1` (`crit_finrank_one_one`) and 0 for
  `t ≥ 2` (`crit_finrank_one`, from `crit_subsingleton_one`). `H₂` is 0 at every grade
  (`crit_finrank_two`), and so is `H_p` for `p ≥ 3` (`crit_finrank_of_three_le`). The vector
  `Pi.single cCA 1` is a sublevel cycle at degree 1 and grade 1 (`crit_single_cCA_mem`), and
  its class there is not zero (`crit_class_cCA_ne_zero`).
- H2. The triangle with the grade `cGrade`: the same table of dimensions
  (`triangle_finrank_zero`, `triangle_finrank_zero_of_lt`, `triangle_finrank_one_of_lt`,
  `triangle_finrank_one_one`, `triangle_finrank_one`, `triangle_finrank_two`,
  `triangle_finrank_of_three_le`). Each value is the H1 value transported by
  `critFlat.finrank_sublevelHomology_eq`; no triangle quotient is computed directly.
- H3. `triangleCycle` is AB + BC + CA, and `critFlat_incl_mulVec_cCA` states that `incl`
  sends CA to it, by a kernel `decide` after rewriting with `critFlat_incl`.
  `triangleCycle_mem` states that it is a degree-1 cycle in grades `≤ 1`, and
  `triangle_class_ne_zero` that its class at grade 1 is not zero, as the image of the class of
  CA under `(critFlat.sublevelHomologyEquiv 1 1).symm`. `triangle_structureMap_one_two` states
  that the degree-1 structure map of `sublevelHomologyPModule tDegree cGrade tD 1` from grade 1
  to grade 2 is zero; it holds because the degree-1 sublevel homology at grade 2 is trivial.

By hand, independently of the contraction: at grade 0 the triangle's sublevel is the path
A–B–C with edges AB and BC, which is connected and has no 1-cycle. At grade 1 the edge CA
closes the cycle AB + BC + CA, which is not a boundary since ABC is not yet present. At grade 2,
`d ABC = AB + BC + CA` fills it, and ABC is not a cycle. This agrees with the values above.
The `*_of_lt` values check that the grade sublevel, not only the degree, enters the
definitions.

## The pivot schedule of a certified matching

`TDA.Persistence.Morse.MatchingSchedule` (namespace `TDA.Persistence.Morse.MatchingInput`)
starts from a #1039 `CertifiedMatching xs` `c` on a finite integer-graded input
`xs : FiniteInput.Input`, described in
[checking a supplied matching](discrete-morse-matchings.md#checking-a-supplied-matching). It
sorts the certified pairs into a schedule, proves that on a valid input this schedule is a
pivot schedule for `FiniteInput.boundary xs` in the sense of
[iterated cancellation along a pivot schedule](#iterated-cancellation-along-a-pivot-schedule),
and names the resulting Morse complex on the critical positions, its filtered contraction and
the isomorphism of
[sublevel homology and the induced isomorphism](#sublevel-homology-and-the-induced-isomorphism).

### Boundary entries and covers

`IsCover xs i j` says that the face at position `i` is contained in the face at position `j`
and has one vertex fewer. Over `ZMod 2`, `coverIncidence xs i j` is `1` when `IsCover xs i j`
holds and the face at position `i` is nonempty, and `0` otherwise.
`boundary_eq_coverIncidence` proves `FiniteInput.boundary xs = coverIncidence xs` for every
input, with no validity hypothesis. The nonemptiness condition is needed: if the face at `i`
is empty and the face at `j` is a singleton, `IsCover xs i j` holds, but the boundary entry is
`0`: in the definition of `FiniteInput.boundary`, with `s` the face at `i` and `t` the face at
`j`, the size test `t.card = s.card - 1 + 2` reads `1 = 2` in `ℕ`. Three lemmas follow:

- `isCover_of_boundary_ne_zero`: on every input, a nonzero boundary entry is a cover;
- `boundary_eq_one_of_isCover`: on a valid input, every cover has coefficient `1`;
- `boundary_ne_zero_iff`: on a valid input, the nonzero entries are exactly the covers.

The proofs of the last two use only the first condition of `Valid xs`, that every listed face
is nonempty. `coverIncidence` reduces in the kernel, while `FiniteInput.boundary` does not
(`Finset.orderEmbOfFin`), so every kernel `decide` of the fixtures on a goal that contains
`FiniteInput.boundary` runs after rewriting with `boundary_eq_coverIncidence`.

### The schedule

`c.schedule` is `c.pairs.insertionSort fun p q => c.rank p.1 ≤ c.rank q.1`: the certified pairs
sorted by non-decreasing rank of the lower face. `List.insertionSort` is a `foldr` of
`List.orderedInsert`, so `schedule` recurses structurally and is computable. Insertion sort is
stable: Mathlib's `List.sublist_insertionSort` keeps every sublist of `c.pairs` that is
`Pairwise` for the relation, and `List.pair_sublist_insertionSort` specializes it to two pairs
`a` before `b` with `c.rank a.1 ≤ c.rank b.1`. So pairs of equal lower-face rank keep their
order in `c.pairs`. The module does not restate stability as a theorem; fixture S3 in
[certificate fixtures](#certificate-fixtures) shows one tie.

- `schedule_perm`: the schedule is a permutation of `c.pairs`, by `List.perm_insertionSort`.
- `schedule_pairwise_rank_le`: it is `Pairwise` for `c.rank p.1 ≤ c.rank q.1`, by
  `List.pairwise_insertionSort`, whose `Std.Total` and `IsTrans` instances for this relation
  the proof supplies.
- `scheduleEndpoints_perm`: `scheduleEndpoints c.schedule` is a permutation of
  `endpoints c.pairs`.

Merge sort is not used. Core's `List.mergeSort` is defined by well-founded recursion and is
`@[irreducible]`, and `decide +kernel` fails to reduce even
`[3, 1, 2].mergeSort = [1, 2, 3]`. The relation `c.rank p.1 ≤ c.rank q.1` is total, so
non-strict sortedness needs no tie rule; stability only fixes which schedule is chosen.

### The arrow chain and the pivot theorem

`rank_lt_of_boundary_ne_zero`: for certified pairs `p ≠ q` with
`FiniteInput.boundary xs p.1 q.2 ≠ 0`, `c.rank q.1 < c.rank p.1`. It takes no validity
hypothesis. The entry makes `(p.1, q.2)` a cover, by `isCover_of_boundary_ne_zero`. This cover
is not a certified pair: it would share `p.1` with `p` and `q.2` with `q`, and since the
certified pairs have distinct endpoints, it would equal both, forcing `p = q`. So
`MatchingInput.arrow` has the matched arrow `q.1 → q.2` and the unmatched arrow `q.2 → p.1`,
and `IsTopologicalRank` gives `c.rank q.1 < c.rank q.2 < c.rank p.1`. With `p = (a i, b i)`
and `q = (a j, b j)`, this is the path `a_j → b_j → a_i` of #1041, also described in
[topological ranks](discrete-morse-matchings.md#topological-ranks), so
`rank a_j < rank a_i`.

`isPivotSchedule_schedule`: for `h : Valid xs`,
`IsPivotSchedule (fun i => (xs.get i).2) (FiniteInput.boundary xs) c.schedule`. The grade is
the list grade of `isFilteredDifferential_boundary`, written as that theorem writes it, so
`ofSchedule` applies with no rewriting. The three conditions come from the certificate:

- the endpoints of the schedule are distinct, by `scheduleEndpoints_perm` and the distinct
  endpoints of `c.isMatching`;
- each pair is a cover with equal grades, by `c.isMatching`, so its coefficient is `1` by
  `boundary_eq_one_of_isCover`;
- for `p` before `q` in the schedule, `p ≠ q`, since the schedule has no duplicate, and
  `c.rank p.1 ≤ c.rank q.1`; a nonzero `FiniteInput.boundary xs p.1 q.2` would give
  `c.rank q.1 < c.rank p.1` by the arrow chain, so the entry is `0`.

Ties are harmless, because the arrow-chain inequality is strict and only non-strict
sortedness is used. By the same argument, any order of tied pairs is a pivot schedule; the
module states the theorem for `schedule` only.

By hand, and not formalized: the hypothesis of `rank_lt_of_boundary_ne_zero` is a list-level
instance of `mnRel` of `TDA.Persistence.Morse.AcyclicMatching`, read through `listFace`. For
`p ≠ q`, `p.1` is a matched lower cell other than `q.1`, and it is a cover of `q.2`, the
partner of `q.1`. The schedule is derived from the rank certificate, not from `mnRel` or
`IsMNAcyclic`, and no Lean statement links them.

### The Morse complex of a certificate

`mem_criticalSet_schedule` states `i ∈ criticalSet c.schedule ↔ i ∈ c.critical`, and
`card_critical_schedule` states `Fintype.card (Critical c.schedule) = c.critical.length`, from
`card_critical` and `critical_length_add`. So the critical generators of the schedule are the
critical positions of the certificate, kept as `Subtype.val`.

`c.morseDifferential` is `criticalDifferential (FiniteInput.boundary xs) c.schedule`, a matrix
on `Critical c.schedule`. It takes no validity hypothesis and is computable. For
`h : Valid xs`:

- `c.morseContraction h` is
  `FilteredContraction.ofSchedule (isFilteredDifferential_boundary xs h) (c.isPivotSchedule_schedule h)`,
  a `FilteredContraction` from `(degree xs, fun i => (xs.get i).2, FiniteInput.boundary xs)`
  onto `(degree xs ∘ Subtype.val, (fun i => (xs.get i).2) ∘ Subtype.val, c.morseDifferential)`;
- `isFilteredDifferential_morseDifferential` states that the Morse differential is a filtered
  differential for these inherited degrees and grades, by `isFilteredDifferential_target`;
- `c.morseHomologyIso h p` is `(c.morseContraction h).sublevelHomologyIso p`: in every degree
  `p`, an isomorphism from `sublevelHomologyPModule` of the boundary complex to
  `sublevelHomologyPModule` of the Morse complex. `sublevelHomologyIso` takes both carriers in
  one universe, and `Fin xs.length` and `Critical c.schedule` both lie in `Type`.

`morseHomologyIso` is `noncomputable`, as `sublevelHomologyIso` is.

### What is not proved here

`TDA.Persistence.Morse.MatchingSchedule` provides none of the following:

- a bridge from
  `sublevelHomologyPModule (degree xs) (fun i => (xs.get i).2) (FiniteInput.boundary xs) p` to
  `sublevelModule (ZMod 2) (FiniteInput.gradeFilter xs h) p` or `simplicialHomologyPModule`,
  and the main theorem of #1041; these are in
  [the simplicial bridge and the Morse persistence theorem](#the-simplicial-bridge-and-the-morse-persistence-theorem);
- an explicit gradient-path formula for `morseDifferential`;
- independence of the Morse differential from the rank of the certificate or from the tie
  order; fixtures S1 and S3 agree in one instance only, and S2 is a different matching;
- a reducer adapter, an ordering of the critical generators or an `Equiv` to `Fin`; the
  reducer order is in
  [the reducer order of a filtered based complex](#the-reducer-order-of-a-filtered-based-complex),
  and the reducer run on the Morse complex is #1061;
- a homology computation by evaluation: `morseHomologyIso` is `noncomputable`.

### Certificate fixtures

The fixtures are in `TDA.Persistence.Morse.MatchingScheduleExamples`, over `ZMod 2`, on the
multi-grade square `square` of `TDA.Persistence.Morse.FiniteInputMatchingExamples`, with
positions 0–10 for A, B, C, D, AB, BC, CD, AD, AC, ABC, ACD. They reuse the position names
`qA` … `qACD`, the grade `sqGrade`, the schedule `sqSchedule` and the matrix `sqCritD` of
fixture H1 in [schedule fixtures](#schedule-fixtures). `sqMorseD l` is the matrix on
`Critical l` with the single entry `d ACD = AD`, and `sqMorseD_sqSchedule` states that it is
`sqCritD` on `sqSchedule`.

- S1. `sqCert` has the pairs of `squarePairs`, (B, AB), (C, BC), (D, CD), (AC, ABC), and the
  rank `sqRank` of `square_check`: 10, 8, 6, 4, 9, 7, 5, 1, 2, 3, 0 for A … ACD. Because
  `square_check` builds its rank with a private helper, `sqCert` restates it as a literal. The
  lower faces AC, D, C, B have ranks 2, 4, 6, 8 (`sqCert_lowerRanks`), so the schedule is
  `sqSchedule`, (AC, ABC), (D, CD), (C, BC), (B, AB) (`sqCert_schedule`). `squarePairs` in its
  own order is not a pivot schedule (`sqCert_pairs_not_isPivotSchedule`). The critical
  positions are A, AD, ACD (`sqCert_critical`, `sqCert_criticalSet`), and the Morse
  differential is `sqMorseD sqCert.schedule` (`sqCert_morseDifferential`).
- S2. `genCert` is the greedy certificate `generate square`, with the pairs (A, AB), (B, BC),
  (C, CD), (AC, ABC). Its schedule is (AC, ABC), (A, AB), (B, BC), (C, CD)
  (`genCert_schedule`); the generated rank, which no fixture states, gives the lower faces AC,
  A, B, C the distinct ranks 1, 2, 4, 6. The critical positions are D, AD, ACD
  (`genCert_critical`, `genCert_criticalSet`), as in the table of
  [generating a matching greedily](discrete-morse-matchings.md#generating-a-matching-greedily),
  and the Morse differential again has the single entry `d ACD = AD`
  (`genCert_morseDifferential`).
- S3. `tieCert` has the pairs of `squarePairs` and the rank `tieRank`
  8, 6, 4, 2, 7, 5, 3, 1, 2, 3, 0, so the lower faces D and AC both have rank 2
  (`tieCert_rank_eq`). The stable sort keeps D, listed before AC in `squarePairs`, first: the
  schedule is (D, CD), (AC, ABC), (C, BC), (B, AB) (`tieCert_schedule`). It is a pivot
  schedule, both by `isPivotSchedule_schedule` and by direct evaluation
  (`tieCert_isPivotSchedule`), as is `sqSchedule`, which has the tied pairs in the other order.
  The critical positions are A, AD, ACD (`tieCert_critical`), and the Morse differential has
  the single entry `d ACD = AD` (`tieCert_morseDifferential`).

The fixture file has 16 theorems. `sqMorseD_sqSchedule` is `rfl`. Ten are a single
`decide +kernel`: `sqCert_lowerRanks`, `sqCert_schedule`, `sqCert_critical`,
`sqCert_criticalSet`, `genCert_schedule`, `genCert_critical`, `genCert_criticalSet`,
`tieCert_rank_eq`, `tieCert_schedule` and `tieCert_critical`. Four rewrite with
`boundary_eq_coverIncidence` and then run `decide +kernel`:
`sqCert_pairs_not_isPivotSchedule` and the three `*_morseDifferential` theorems, which first
unfold `CertifiedMatching.morseDifferential`. `tieCert_isPivotSchedule` proves its first
conjunct by `isPivotSchedule_schedule square_valid` and its second by the same rewrite and
`decide +kernel`. The `isMatching` and `isTopologicalRank` fields of `sqCert` and `tieCert`
are `decide +kernel`. No fixture uses `norm_num`, `fin_cases`, `ofSchedule_congr` or
`square_boundary`, and none computes homology.

By hand, for S2 in schedule order: cancelling (AC, ABC) turns `d ACD = CD + AD + AC` into
`AB + BC + CD + AD`, and the three later steps leave that column unchanged, since its
coefficients at A, B and C are 0; on the critical rows it is AD. The column of AD changes from
`A + D` to `B + D`, `C + D` and then 0, after (A, AB), (B, BC) and (C, CD). S1 and S3 give the
same Morse differential from two orders of the same pairs; this is one instance, not a theorem
about order independence.

## The simplicial bridge and the Morse persistence theorem

`TDA.Persistence.Morse.SimplicialBridge` has two parts, over `ZMod 2`. The simplicial bridge,
in namespace `TDA.Persistence.Morse.SimplicialBridge`, involves no matching: for a finite
input `xs` with `h : Valid xs`, it identifies the persistence module
`sublevelHomologyPModule` of the boundary complex
`(degree xs, fun i => (xs.get i).2, FiniteInput.boundary xs)` of
[sublevel homology and the induced isomorphism](#sublevel-homology-and-the-induced-isomorphism)
with the simplicial sublevel persistence module
`sublevelModule (ZMod 2) (FiniteInput.gradeFilter xs h) p` of the represented complex. The
main theorem of #1041, in namespace `TDA.Persistence.Morse.MatchingInput.CertifiedMatching`,
composes the inverse bridge with `morseHomologyIso` of
[the Morse complex of a certificate](#the-morse-complex-of-a-certificate).

### The bridge on list positions

The route stays on the list positions `Fin xs.length` and uses no `Fin.cast`; the proof of
`boundaryCycleCoordinates_eq_zero_iff` is the only proof of the module that opens the instance
`FiniteInput.faceFintype`.

- `sublevelSupported_iff_prefixSupported`: on a valid input, a vector is supported in grades
  `≤ a` exactly when it is supported in the positions before `sublevelStage xs a`.
- `cycleInput_iff_mem_sublevelCycles`: with no validity hypothesis,
  `FiniteInput.CycleInput xs p a v` is membership of `v` in the sublevel cycles of the boundary
  complex in degree `p` and grade `a`.
- `boundaryCycleCoordinates xs p a` is the reducer's `rawCycleCoordinates xs p a` restricted to
  these sublevel cycles, a computable linear map to `BasisIndex xs p a → ZMod 2`.
- `boundaryCycleCoordinates_eq_zero_iff`: on a valid input, a sublevel cycle has zero
  coordinates exactly when it is a sublevel boundary. Forward, the executable filling
  `fillingVector` is a degree-`p + 1` chain in grades `≤ a` whose boundary is the cycle
  (`fillingVector_supported`, `fillingVector_boundary`). Backward, for a sublevel boundary
  `D w` with `D = FiniteInput.boundary xs`, the simplicial chain `simplicialChain … w`,
  included into the grade-`a` sublevel complex, has boundary `vectorSublevelCycle … (D w)`
  (`simplicialChain_boundary`, `boundary_chainIncl`), so
  `rawCycleCoordinates_eq_zero_iff_boundary` gives zero coordinates.
  `ker_boundaryCycleCoordinates` restates this as the equality of the kernel with the
  submodule that `sublevelHomology` divides by.
- `boundaryCycleCoordinates_surjective`: on a valid input, every coordinate vector is
  attained; the `i`-th basis vector is the coordinate vector of the cycle of
  `basisRecord xs p a i` (`rawCycleCoordinates_basisRecord`).

`boundaryHomologyEquiv h p a` is the `noncomputable` `LinearEquiv` from `sublevelHomology` of
the boundary complex in degree `p` and grade `a` to
`simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p` obtained from the kernel
equality, `quotKerEquivOfSurjective` and the inverse of `sublevelCoordinates xs h p a`.
`boundaryHomologyEquiv_mk` states that it sends the class of a sublevel cycle `z` to
`vectorSublevelClass xs h p a z _`, the actual simplicial class of the cycle with the face
coefficients of `z`, by `rawCycleCoordinates_correct`. Every element of the quotient is such a
class, so this determines the equivalence. `boundaryHomologyEquiv_naturality` follows from
`vectorSublevelClass_naturality`: the equivalence commutes with `sublevelHomologyMap` and
`simplicialHomologyIncl`.

`boundaryHomologyIso h p` is `NatIso.ofComponents` of the components
`(boundaryHomologyEquiv h p a).toModuleIso`: an isomorphism
`sublevelHomologyPModule (degree xs) (fun i => (xs.get i).2) (FiniteInput.boundary xs) p ≅ sublevelModule (ZMod 2) (gradeFilter xs h) p`
of persistence modules over `ℤ`. `boundaryHomologyIso_hom_app` and
`boundaryHomologyIso_inv_app` identify its components with the equivalence and its inverse,
by `rfl`, and `finrank_sublevelHomology_boundary` equates the dimensions at every degree and
grade.

### The Morse persistence theorem

For `c : CertifiedMatching xs` and `h : Valid xs`, `c.morseSublevelModuleIso h p` is
`(boundaryHomologyIso h p).symm ≪≫ c.morseHomologyIso h p`. In every degree `p` it is a natural
isomorphism from `sublevelModule (ZMod 2) (gradeFilter xs h) p` to
`sublevelHomologyPModule (degree xs ∘ Subtype.val) ((fun i => (xs.get i).2) ∘ Subtype.val) c.morseDifferential p`,
the grade-sublevel homology persistence module of the Morse complex on the critical
generators. It runs in the direction of the projection of the contraction
`c.morseContraction h`.

- `morseSublevelModuleIso_hom_app` and `morseSublevelModuleIso_inv_app`, both `rfl`: the
  components are the inverse bridge followed by `homologyProj`, and `homologyIncl` followed by
  the bridge.
- `morseSublevelModuleIso_hom_vectorSublevelClass`: the actual simplicial class
  `vectorSublevelClass xs h p a v hv` of a sublevel cycle vector `v` goes to the class of
  `proj v` in the Morse complex.
- `finrank_simplicialHomology_eq`: at every degree and grade, the simplicial sublevel homology
  and the sublevel homology of the Morse complex have equal `Module.finrank`.
- `rankOfStructureMap_sublevelModule_eq`: for `a ≤ b`, the structure maps of the two
  persistence modules have equal `rankOfStructureMap`, by `rankOfStructureMap_iso`.

### Executable and semantic parts

Computable: `coverIncidence`, `schedule` and `morseDifferential` of
`TDA.Persistence.Morse.MatchingSchedule`, and `boundaryCycleCoordinates`. The fixtures of
[bridge fixtures](#bridge-fixtures) evaluate the Morse differential, the critical generators with their degrees and grades, the
loop's `CycleInput`, the boundary of its filling and support conditions by `decide +kernel`.
Semantic: `boundaryHomologyEquiv`, `boundaryHomologyIso` and `morseSublevelModuleIso` are
`noncomputable`, and the fixtures' homology dimensions, ranks and diagrams are proved, not
evaluated: on the three-generator Morse complex directly, and on the square by transport
through the main theorem and, for the diagrams, by `rank_sublevelHomologyMap`.

### Scope of the bridge

`TDA.Persistence.Morse.SimplicialBridge` and its fixture file provide none of the following:

- an interval module or an interval decomposition over `ℤ`, or a barcode statement other than
  the diagrams `dgm` of the square in degrees 1 and 0 (fixture M7);
- agreement with the reducer's barcode or diagrams; this is #1061;
- a chain-level isomorphism with `simplicialChainComplex`: the contraction `morseContraction`
  is of the based boundary-matrix complex of the input, the face-basis form of the simplicial
  chain complex that #1041 says to reuse (#203, #196), and it is not transported to
  `simplicialChainComplex` as a `HomologicalComplex`; the bridge is stated on sublevel
  homology only;
- independence of the Morse complex from the certificate (fixture M6 is one instance), a
  gradient-path formula, or a coefficient ring other than `ZMod 2`;
- a source attribution; see [comparison with MN13](#comparison-with-mn13).

### Bridge fixtures

The fixtures are in `TDA.Persistence.Morse.SimplicialBridgeExamples`, over `ZMod 2`, on the
multi-grade square `square` with the certificate `sqCert`, the greedy certificate `genCert` and
the position names of [certificate fixtures](#certificate-fixtures). By hand: below grade 0 the
sublevel complex is empty; at grade 0 it is the path A–B–C–D; at grade 1 the edge AD closes the
loop AB + BC + CD + AD, which is not a boundary; at grade 2, over `ZMod 2`, `∂ABC + ∂ACD` is
the loop, the degree-1 cycles have dimension 5 − 4 + 1 = 2 and the two triangle boundaries are
independent, so `H₁` and `H₂` vanish. The Morse complex of `sqCert`, with A, AD, ACD in degrees
and grades 0, 1, 2 and the single entry `d ACD = AD`, gives the same table directly.

- M1. `MC` is `Critical sqCert.schedule`, with the inherited degrees `mDegree` and grades
  `mGrade`. `mA`, `mAD` and `mACD` are the critical generators A, AD and ACD, and `mc_cases`
  states that there are no others. `mDiff` is the matrix whose only nonzero entry is
  `d ACD = AD`, and `morseDifferential_eq` states `sqCert.morseDifferential = mDiff`.
- M2. The sublevel homology of the Morse complex. `H₀` has dimension 1 for `t ≥ 0`
  (`morse_finrank_zero`) and is trivial for `t < 0` (`morse_subsingleton_zero_of_lt`). `H₁` is
  trivial for `t < 1` (`morse_subsingleton_one_of_lt`), has dimension 1 at `t = 1`
  (`morse_finrank_one_one`) and is trivial for `t ≥ 2` (`morse_subsingleton_one`). `H₂` is
  trivial at every grade (`morse_subsingleton_two`), and so is `H_p` for `p ≥ 3`
  (`morse_subsingleton_of_three_le`).
- M3. With `sqSublevel t` the grade-`t` sublevel complex of the square, the same table for
  `Module.finrank (ZMod 2) (simplicialHomology (sqSublevel t) (ZMod 2) p)`
  (`square_finrank_zero`, `square_finrank_zero_of_lt`, `square_finrank_one_of_lt`,
  `square_finrank_one_one`, `square_finrank_one`, `square_finrank_two`,
  `square_finrank_of_three_le`). Each value is the M2 value transported by
  `finrank_simplicialHomology_eq`; no simplicial homology quotient is computed directly.
- M4. For all grades `a ≤ b`, `square_rankOfStructureMap_one` states that the rank of the
  degree-1 structure map of `sublevelModule (ZMod 2) (gradeFilter square square_valid) 1` from
  `a` to `b` is `1` if `a = 1` and `b = 1`, and `0` otherwise: the rank invariant of the
  interval `[1,2)` of `ℤ`. `square_rankOfStructureMap_zero` states that in degree 0 it is `1`
  if `0 ≤ a` and `0` otherwise: the rank invariant of `[0,∞)`.
- M5. `sqLoop` is AB + BC + CD + AD and `sqFill` is ABC + ACD, on the positions of `square`.
  `sqLoop_cycleInput` states `CycleInput square 1 1 sqLoop`, and `boundary_mulVec_sqFill` that
  the boundary of `sqFill` is `sqLoop`. `sqLoop_class_ne_zero` states that the actual class
  `vectorSublevelClass square square_valid 1 1 sqLoop _` is not zero, and `sqLoop_class_filled`
  that `simplicialHomologyIncl` from grade 1 to grade 2 sends it to zero.
- M6. For `genCert`, with critical positions D, AD, ACD, `genCert_morse_finrank_one_one`
  states that the degree-1 sublevel homology of its Morse complex has dimension 1 at grade 1,
  and `genCert_rankOfStructureMap_one` that its degree-1 persistence module has the rank
  invariant of `[1,2)`. Both are read off the square's simplicial side (M3, M4) through
  `finrank_simplicialHomology_eq` and `rankOfStructureMap_sublevelModule_eq` for `genCert`.
- M7. `square_dgm_one` states
  `(dgm (ZMod 2) (gradeFilter square square_valid) 1).points = {(1, 2)}`, and `square_dgm_zero`
  that in degree 0 the points are `{(0, ⊤)}`, with `⊤ : WithTop ℤ` the essential end. Both are
  derived from M4 by `rank_sublevelHomologyMap` and `dgm_isPositive`, not from the reducer.

The fixture file has 10 public definitions and 26 public theorems. `mA`, `mAD` and `mACD`
prove membership in the critical set by `decide +kernel`, and the other seven definitions are
written out. Of the theorems:

- four end in `decide +kernel`: `mc_cases` after `revert`, `morseDifferential_eq` after
  rewriting with `sqCert_morseDifferential`, and `sqLoop_cycleInput` and
  `boundary_mulVec_sqFill` after rewriting with `boundary_eq_coverIncidence`, the first also
  unfolding `CycleInput`;
- the seven M2 theorems argue on the three-generator Morse complex, through private lemmas;
- the seven M3 theorems and the two M6 theorems are term proofs that transport values through
  `finrank_simplicialHomology_eq` or `rankOfStructureMap_sublevelModule_eq`;
- the two M4 theorems rewrite with `rankOfStructureMap_sublevelModule_eq` and then argue on the
  Morse side with M2 values and, in degree 0, private lemmas;
- the two M5 class theorems go through `boundaryHomologyEquiv_mk`, with side goals closed by
  `decide +kernel`;
- the two M7 theorems count diagram points through `rank_sublevelHomologyMap` and
  `dgm_isPositive`.

In this sense the bar `[1,2)` is certified: M4 gives the rank invariant of `[1,2)` for every
`a ≤ b`, M7 proves that the square's degree-1 `dgm`, the library's diagram of simplicial
sublevel homology, is `{(1, 2)}`, and M5 exhibits the class born at grade 1 and filled at
grade 2. These modules formalize no interval module over `ℤ` and no interval decomposition,
and state no agreement with the reducer's output (#1061).

## The reducer order of a filtered based complex

`TDA.Persistence.Morse.ReducerOrder` (namespace `TDA.Persistence.Morse.ReducerOrder`) orders
the generators of a filtered based complex `(ι, degree, grade, D)` so that, over a field, its
differential satisfies the input conditions of the column reducer of
`TDA.Persistence.Reduction`. The module runs no reduction.

### What the reducer needs

The reducer's `matrixReductionTrace` runs on a square matrix over `Fin m`. Its normal-form
theorem `matrixReductionTrace_normalForm_input degree D hD2 hstrict hdegree`
(`FilteredNormalForm/NormalMatrix.lean`), which
`matrixReductionTrace_originalHomologyMap_rank_formula`
(`FilteredNormalForm/OriginalHomology.lean`) consumes, needs three hypotheses: `D * D = 0`,
`StrictBoundary D` (a nonzero entry in row `r` and column `c` has `r < c`) and
`LowersDegree degree D` (such an entry has `degree c = degree r + 1`). `StrictBoundary` and
`LowersDegree` are stated under `[Field k]`. The carrier `ι` of a filtered based complex is not
`Fin m`, and its inherited order need not be triangular: fixture F4 of [fixtures](#fixtures)
shows that a valid cancellation breaks it, and fixture R2 of
[reducer order fixtures](#reducer-order-fixtures) shows the same for the Morse complex of a
certified matching on a valid input.

### The key and the sort

For a carrier with `[LinearOrder ι]`, which serves as the stable identity of the generators,
`key degree grade x` is `toLex (grade x, toLex (degree x, x))` in `ℤ ×ₗ ℕ ×ₗ ι`: grade first,
then degree, then the generator itself.

- `key_injective`: the key determines the generator.
- `key_lt`: `grade x ≤ grade y` and `degree y = degree x + 1` give `key x < key y`.
- `key_lt_of_ne_zero`: over a commutative ring, a nonzero entry `D r c` of a filtered
  differential has `key r < key c`, from `grade r ≤ grade c` and `degree c = degree r + 1`.

Grade first makes the grades monotone along the order. Degree second separates a nonzero entry
at equal grades, the case of F4 and R2. The generator third makes the key injective. On the
Morse carrier `Critical c.schedule` of a certificate `c`, a subtype of `Fin xs.length`, the
order of the generators is the list position.

`sortList degree grade L` is `List.insertionSort` of `L` by `key`. `sortList_perm` states that
it is a permutation of `L`, `pairwise_sortList_le` that it is sorted by non-decreasing key,
`pairwise_sortList` that it is strictly increasing in key when `L` has no duplicates, and
`sortList_eq_of_perm` that it depends on `L` only up to permutation. On a finite carrier,
`sortedGenerators degree grade` is `Quotient.liftOn` of `sortList` over the multiset
`Finset.univ.val`, well defined by `sortList_eq_of_perm`; it chooses no enumeration of the
carrier. `sortedGenerators_eq` states that it is `sortList` of any duplicate-free list of all
generators, and `mem_sortedGenerators`, `pairwise_sortedGenerators`, `nodup_sortedGenerators`
and `length_sortedGenerators` (`= Fintype.card ι`) follow.

Insertion sort is used because `decide +kernel` reduces it; merge sort does not reduce there,
as [the schedule](#the-schedule) records. Mathlib's `Finset.sort` is built on merge sort.

### The reducer order and the reducer matrix

`reducerEquiv degree grade : Fin (sortedGenerators degree grade).length ≃ ι` is
`List.Nodup.getEquivOfForallMemList` of the sorted list: position `i` goes to the `i`-th sorted
generator (`reducerEquiv_apply`, `rfl`), and the inverse is computed by `List.idxOf`.

- `key_strictMono`: the key is strictly increasing along `reducerEquiv`.
- `lt_iff_key_lt`: `i < j` exactly when `key (reducerEquiv … i) < key (reducerEquiv … j)`.
- `monotone_grade`: `grade ∘ reducerEquiv degree grade` is monotone.

`reducerMatrix degree grade D` is `D.submatrix e e` with `e = reducerEquiv degree grade`, a
matrix over `Fin (sortedGenerators degree grade).length`. For a filtered differential `D`:

- over a commutative ring, `reducerMatrix_sq_zero` gives `M * M = 0` and
  `isFilteredDifferential_reducerMatrix` states that `M` is a filtered differential for the
  transported degree `degree ∘ e` and grade `grade ∘ e`;
- over a field, `strictBoundary_reducerMatrix` gives `StrictBoundary M`, from the general
  `strictBoundary_submatrix` for any `e : Fin m ≃ ι` along which `key` is strictly increasing,
  and `lowersDegree_reducerMatrix` gives `LowersDegree (degree ∘ e) M`;
- over a field with decidable equality, `reducerMatrix_normalForm_input` is
  `matrixReductionTrace_normalForm_input` applied to `M` with these three hypotheses, so the
  existing reducer's normal-form conclusions hold for it. No reducer declaration is changed.

### Identities of the generators

`reducerEquiv` is an equivalence onto the original carrier, so the generators keep their
identities; on the Morse carrier of a certificate these are the original list positions. `reducerContraction` is the
identity filtered contraction `FilteredContraction.refl degree grade D` transported by
`reindex` along `(reducerEquiv degree grade).symm` and restated by `copy`, a filtered
contraction from `(degree, grade, D)` onto `(degree ∘ e, grade ∘ e, reducerMatrix degree grade D)`.
Its projection and inclusion are the identity matrix read in the reducer order, and its
homotopy is zero (`reducerContraction_proj`, `reducerContraction_incl`,
`reducerContraction_htpy`, all `rfl`). For `ι : Type`, `reducerHomologyIso degree grade D p` is
its `sublevelHomologyIso p`, an isomorphism of the grade-sublevel homology persistence modules
of [sublevel homology and the induced isomorphism](#sublevel-homology-and-the-induced-isomorphism)
of the complex and of its reducer order, in every degree `p`.

### Executable and semantic parts of the order

Computable: `key`, `sortList`, `sortedGenerators`, `reducerEquiv`, `reducerMatrix` and
`reducerContraction`. The fixtures evaluate sorts and reordered matrices by `decide +kernel`.
Semantic: `reducerHomologyIso` is `noncomputable`, as `sublevelHomologyIso` is, and the other
statements are propositions.

### Scope of the reducer order

`TDA.Persistence.Morse.ReducerOrder` and its fixture file provide none of the following:

- a reducer run on Morse chain data, its pivot pairs, occurrences or diagrams, or an agreement
  with `dgm` or with `FiniteInput.outputDiagram`; the reducer output of a filtered based
  complex and its rank semantics are in
  [the graded reducer output and its rank semantics](#the-graded-reducer-output-and-its-rank-semantics),
  and the run on the Morse complex of a certificate and the agreement with `dgm` remain for
  #1061;
- independence of the reducer's output from the tie order beyond what `sortList_eq_of_perm`
  gives, namely independence of the enumeration that is sorted;
- a gradient-path formula, reducer statements over a ring other than a field, or a runtime
  bound or speedup claim;
- a source attribution; see [comparison with MN13](#comparison-with-mn13).

### Reducer order fixtures

The fixtures are in `TDA.Persistence.Morse.ReducerOrderExamples`, over `ZMod 2`.

- R1. On the survivors `W` of the F4 cancellation of `(a, b)` in `wD`, with the inherited
  degrees `rDegree` and grades `rGrade`, the reduced differential `reducedDifferential wD 0 3`
  is a filtered differential (`tie_isFilteredDifferential_reduced`) with the single entry
  `d' s = r`. In the inherited survivor order `s, r` (`[wS, wR].get`) its entry in row 1 and
  column 0 is nonzero, so it is not `StrictBoundary` (`tie_inherited_not_strictBoundary`).
  `sortedGenerators` is `[wR, wS]` (`tie_sortedGenerators`); the reducer matrix has the single
  nonzero entry in row 0 and column 1 (`tie_reducerMatrix`) and is `StrictBoundary`
  (`tie_strictBoundary`).
- R2. `path` is the path A–B–C at grade 0, listed A, B, AB, C, BC, and is valid
  (`path_valid`). `pathCert` certifies the single pair (B, BC), with critical positions A, AB, C
  (`pathCert_critical`). By hand, `d AB = (A + B) + (B + C) = A + C` over `ZMod 2`, and
  `pathCert_morseDifferential` states that the Morse differential is the written-out `pDiff`,
  whose nonzero entries are exactly `d AB = A + C`. C occurs in `d AB` but is listed after AB:
  in the inherited position order A, AB, C the entry in row 2 and column 1 is nonzero
  (`path_inherited_not_strictBoundary`). The keys of A, C, AB are (0, 0, A), (0, 0, C),
  (0, 1, AB), so `sortedGenerators` is A, C, AB (`path_sortedGenerators`), and `sortList` of the
  enumeration AB, C, A gives the same list (`path_sortList`). The reducer matrix has exactly the
  nonzero entries in rows 0 and 1 of column 2 (`path_reducerMatrix`) and is `StrictBoundary`
  (`path_strictBoundary`).
- R3. On the multi-grade square of [certificate fixtures](#certificate-fixtures), with the
  inherited degrees `sDegree` and grades `sGrade`, the reducer order of `sqCert` is A, AD, ACD
  and that of `genCert` is D, AD, ACD, both with grades 0, 1, 2
  (`sqCert_sortedGenerators`, `genCert_sortedGenerators`), so it is the position order. For
  both, the reducer matrix of the Morse differential has the single nonzero entry in row 1 and
  column 2, `d ACD = AD` (`sqCert_reducerMatrix`, `genCert_reducerMatrix`).

The fixture file has 20 public definitions (3 `abbrev`, 17 `def`) and 17 public theorems. The
definitions are written out; the `isMatching` and `isTopologicalRank` fields of `pathCert` and
the memberships in `cA`, `cAB` and `cC` are `decide +kernel`, and the bounds in `pA`–`pBC` are
`decide`. Of the theorems:

- seven are a single `decide +kernel`: `tie_sortedGenerators`, `tie_reducerMatrix`,
  `pathCert_critical`, `path_sortedGenerators`, `path_sortList`, `sqCert_sortedGenerators` and
  `genCert_sortedGenerators`;
- `path_valid` is `FiniteInput.validBool_iff` applied to a `decide +kernel`;
- four end in `decide +kernel` after a rewrite: `pathCert_morseDifferential` after
  `CertifiedMatching.morseDifferential` and `boundary_eq_coverIncidence`, `path_reducerMatrix`
  after `pathCert_morseDifferential`, and `sqCert_reducerMatrix` and `genCert_reducerMatrix`
  after `sqCert_morseDifferential` and `genCert_morseDifferential` of
  `TDA.Persistence.Morse.MatchingScheduleExamples`;
- two exhibit the nonzero entry below the diagonal, with side goals closed by `decide +kernel`
  and `decide`: `tie_inherited_not_strictBoundary`, and `path_inherited_not_strictBoundary`
  after rewriting with `pathCert_morseDifferential`;
- three are term proofs: `tie_isFilteredDifferential_reduced` by
  `isFilteredDifferential_reduced`, and `tie_strictBoundary` and `path_strictBoundary` by
  `strictBoundary_reducerMatrix`, the latter with
  `isFilteredDifferential_morseDifferential path_valid`.

The two negative fixtures exhibit the offending entry rather than decide `StrictBoundary`; the
matrix equalities are stated against `Matrix.of`, which `decide +kernel` evaluates. No fixture
runs the reducer or computes homology.

## The graded reducer output and its rank semantics

`TDA.Persistence.Morse.ReducerDiagram` (namespace `TDA.Persistence.Morse.ReducerDiagram`)
reads the output of the column reducer of `TDA.Persistence.Reduction` on a square matrix over
`Fin m` as occurrences and diagrams over integer grades, and proves that, under the reducer's
input conditions and monotone grades, their slice counts are the ranks of the grade-sublevel
homology persistence module of
[sublevel homology and the induced isomorphism](#sublevel-homology-and-the-induced-isomorphism).
On the reducer order of
[the reducer order of a filtered based complex](#the-reducer-order-of-a-filtered-based-complex),
this gives a diagram over `ℤ` for every filtered differential over a field.
`TDA.Persistence.DiagramRankUniqueness` (namespace `TDA.Persistence`) proves that a positive
diagram is determined by its slice counts.

### The reducer output

Over a field `k` with decidable equality, for `D : Matrix (Fin m) (Fin m) k`,
`degree : Fin m → ℕ` and `grade : Fin m → ℤ`:

- `reduced D` is `replay D (matrixReductionTrace D)`, the reduced matrix of the reducer.
- `pivotPairs D` lists, over the columns `j` in increasing order, the pairs `(i, j)` whose
  reduced column `j` has pivot row `i` (`columnPivot`, its greatest nonzero row);
  `mem_pivotPairs` states this membership.
- `essentialIndices D` lists the indices whose reduced column is zero and which are no pivot
  row; `mem_essentialIndices` identifies them with `IsEssential (reduced D)`.
- `pairOccurrence degree grade (i, j)` is `none` when `grade i = grade j`, and otherwise the
  `FiniteInput.Occurrence` with degree `degree i`, birth `grade i` and finite death `grade j`.
- `occurrences degree grade D` lists the `pairOccurrence` values of the pivot pairs that are
  not `none`, followed by the essential indices with essential death, and
  `diagram degree grade D p : Diagram ℤ` collects the points `Occurrence.point` of the
  degree-`p` occurrences, with multiplicity.

These follow `FiniteInput.reduced`, `pivotPairs`, `essentialIndices`, `pairOccurrence`,
`occurrences` and `outputDiagram`, with the finite input replaced by `(degree, grade, D)`. On
the boundary matrix `FiniteInput.boundary xs`, with `FiniteInput.degree xs` and the grades of
`xs`, `occurrences_boundary` and `diagram_boundary` state by `rfl` that `occurrences` is
`FiniteInput.occurrences xs` and `diagram` is `FiniteInput.outputDiagram xs p`. `FiniteInput`
and the reducer are unchanged.

`decidableStrictBoundary` and `decidableLowersDegree` decide `StrictBoundary D` and
`LowersDegree degree D` entry by entry over `Fin m`.

### Prefixes and sublevel homology

`stage grade a` is the number of indices `i` with `grade i ≤ a`; `stage_le` bounds it by `m`
and `stage_mono` states that it is monotone in `a`. For monotone `grade`,
`grade_le_iff_lt_stage` states that `grade i ≤ a` exactly when `i.val < stage grade a`: the
indices of grade at most `a` are the first `stage grade a` indices. Hence, for monotone
`grade`:

- `sublevelSupported_iff_prefixSupported`: support in grades `≤ a` is support in the prefix
  `stage grade a`;
- `sublevelCycles_eq_originalCycleSpace`: `sublevelCycles degree grade D p a` is the reducer's
  prefix cycle space `originalCycleSpace degree D p (stage grade a)`;
- `mem_sublevelBoundaries_iff_originalBoundary`: the sublevel boundaries in grades `≤ a` are
  the reducer's prefix boundaries `OriginalBoundary` at `stage grade a`.

The reducer's `originalHomology` at a prefix is the prefix cycle space modulo the kernel of
`originalLiveMap`, and `originalHomology_kernel_eq_boundaries` identifies that kernel with the
prefix boundaries. For any normal-form data `R`, `V`, `W` of `D` with the hypotheses of
`originalHomology`, `prefixHomologyEquiv` is the resulting linear equivalence from
`sublevelHomology degree grade D p a` to `originalHomology … p (stage grade a)`, built from
`Submodule.Quotient.equiv` and `LinearEquiv.ofEq`. It keeps the representing cycle
(`prefixHomologyEquiv_mk`, `rfl`), and `prefixHomologyEquiv_naturality` carries the sublevel
structure map `a ≤ b` to the reducer's `originalHomologyMap` from `stage grade a` to
`stage grade b`; it is checked on representatives with `originalHomologyMap_mk`. So the two
maps have ranges of equal dimension (`finrank_range_sublevelHomologyMap_eq`).

### The rank theorem

The slice count of a diagram at `a ≤ b` is the number of its points `(b', d)`, with
multiplicity, such that `b' ≤ a` and `b < d`: inclusive birth and strict death, the predicate
of `rank_sublevelHomologyMap` and of `RealBarcode.multiset_eq_of_rankCounts_eq`.

- `countP_diagram`: for monotone `grade` and `a ≤ b`, the slice count of
  `diagram degree grade D p` is the cardinality of
  `deathSurvivorFinset degree (reduced D) p (stage grade a) (stage grade b)` plus that of
  `essentialSurvivorFinset degree (reduced D) p (stage grade a)`, the right side of the
  reducer's rank formula `matrixReductionTrace_originalHomologyMap_rank_formula` at the stages
  of `a` and `b`. A pivot pair `(i, j)` counts there when `degree i = p`,
  `i.val < stage grade a` and `stage grade b ≤ j.val`, that is, `grade i ≤ a` and
  `b < grade j`. An equal-grade pair would need `grade i ≤ a ≤ b < grade j = grade i`, so it
  counts for no `a ≤ b`; this is why `pairOccurrence` may drop it.
- `rankOfStructureMap_eq_countP`: under `D * D = 0`, `StrictBoundary D`,
  `LowersDegree degree D` and `Monotone grade`, the rank of the structure map `a ≤ b` of
  `sublevelHomologyPModule degree grade D p` is the slice count of `diagram degree grade D p`
  at `a ≤ b`. The proof takes the normal-form data of
  `matrixReductionTrace_normalForm_input`, applies `finrank_range_sublevelHomologyMap_eq` and
  `countP_diagram`, and closes with the rank formula.
- `diagram_isPositive`: under the same hypotheses, every point has birth strictly below death.
  A pivot pair `(i, j)` has `i < j` because the reduced matrix is `StrictBoundary`, so
  `grade i ≤ grade j` by monotonicity, and the kept pairs have `grade i ≠ grade j`; essential
  points have death `⊤`.
- `eq_diagram_of_rankCounts`: under the same hypotheses, a positive diagram whose slice counts
  are the ranks of `sublevelHomologyPModule degree grade D p` is `diagram degree grade D p`.

### Uniqueness from slice counts

In `TDA.Persistence.DiagramRankUniqueness`, over any `LinearOrder α`,
`multiset_eq_of_sliceCounts_eq` states that two finite multisets of points in
`α × WithTop α`, each point with birth strictly below death (`⊤` allowed as death), with equal
slice counts at all `a ≤ b`, are equal; `Diagram.eq_of_sliceCounts_eq` states the same for
positive diagrams. The births and finite deaths of both multisets lie on one finite grid
`Finset.orderEmbOfFin`. On it each multiset is `ofIndexBars` of a finite index barcode, the slice
counts become interval counts of those barcodes (`ofIndexBars_countP_grades`), and
finite-barcode uniqueness (`rankBarcode_barcodeModule`, `rank_barcodeMap`, with a barcode
module over `ℚ`) recovers them. `RealBarcode.multiset_eq_of_rankCounts_eq` of
`TDA.Persistence.RealBarcodeRankUniqueness` is proved as its instance over `ℝ`; its statement
is unchanged.

### Filtered based complexes

For `ι : Type` with `[LinearOrder ι] [Fintype ι]`, over a field with decidable equality,
`reducerOccurrences degree grade D` and `reducerDiagram degree grade D p` are `occurrences` and
`diagram` of `reducerMatrix degree grade D`, with the degree `degree ∘ reducerEquiv degree grade`
and the grade `grade ∘ reducerEquiv degree grade`. For `IsFilteredDifferential degree grade D`:

- `rankOfStructureMap_eq_countP_reducerDiagram`: the rank of the structure map `a ≤ b` of
  `sublevelHomologyPModule degree grade D p`, the module of the original complex, is the slice
  count of `reducerDiagram degree grade D p` at `a ≤ b`. It transports the rank theorem along
  `reducerHomologyIso` (`rankOfStructureMap_iso`), with the hypotheses
  `reducerMatrix_sq_zero`, `strictBoundary_reducerMatrix`, `lowersDegree_reducerMatrix` and
  `monotone_grade`.
- `reducerDiagram_isPositive`: `reducerDiagram degree grade D p` is positive.
- `eq_reducerDiagram_of_rankCounts`: a positive diagram whose slice counts are the ranks of
  `sublevelHomologyPModule degree grade D p` is `reducerDiagram degree grade D p`.

### Executable and semantic parts of the output

Computable: `reduced`, `pivotPairs`, `essentialIndices`, `pairOccurrence`, `occurrences`,
`diagram`, `stage`, `reducerOccurrences`, `reducerDiagram` and the two instances. The fixtures
evaluate `pivotPairs`, `essentialIndices`, `occurrences` and `diagram` by `decide +kernel`, and
decide `StrictBoundary` and `LowersDegree` through the two instances.
`FiniteInput.occurrences` has a stored-pivot `@[csimp]` implementation; the generic
`occurrences` has none, so its compiled evaluation may repeat the reduction for each entry.
Kernel `decide` is unaffected, and no runtime claim is made.
Semantic: `prefixHomologyEquiv` is `noncomputable`, and the other statements are propositions.

### Scope of the reducer output

`TDA.Persistence.Morse.ReducerDiagram`, `TDA.Persistence.DiagramRankUniqueness` and the fixture
file provide none of the following:

- a certificate-level run of the reducer on the Morse complex of a certified matching, or an
  agreement of such a run with `dgm` or with `FiniteInput.outputDiagram`; these remain for
  #1061;
- a change to the statement of `RealBarcode.multiset_eq_of_rankCounts_eq` or to
  `dgm_eq_of_vertexMaps`;
- an interval module or an interval decomposition over `ℤ`;
- independence of the occurrence list `reducerOccurrences` from the tie order of the reducer
  order, and a declaration stating that `reducerDiagram` does not depend on it;
- reducer statements over a ring other than a field, or a runtime bound or speedup claim;
- a source attribution; see [comparison with MN13](#comparison-with-mn13).

### Reducer output fixtures

The fixtures are in `TDA.Persistence.Morse.ReducerDiagramExamples`, over `ZMod 2`, on
written-out matrices.

- P1. `triD` is the boundary matrix of a hollow triangle on `Fin 6`: vertices `0, 1, 2` at
  grade 0, edges `3 = 01` and `4 = 12` at grade 1 and `5 = 02` at grade 2 (`triDegree`,
  `triGrade`). The four hypotheses of the rank theorem hold (`tri_sq_zero`,
  `tri_strictBoundary`, `tri_lowersDegree`, `tri_monotone`). Columns 3 and 4 keep their pivots
  1 and 2; column 5 has pivot 2, becomes `0 + 1` after adding column 4 and zero after adding
  column 3. So the pivot pairs are `(1, 3)` and `(2, 4)` (`tri_pivotPairs`), the essential
  indices `0` and `5` (`tri_essentialIndices`), and the occurrences are
  `[⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨0, 0, .essential⟩, ⟨1, 2, .essential⟩]`
  (`tri_occurrences`). The degree-0 diagram is `{(0, 1), (0, 1), (0, ⊤)}` and the degree-1
  diagram `{(2, ⊤)}` (`tri_diagram_zero`, `tri_diagram_one`). In degree 0 the structure maps
  `0 ≤ 0` and `0 ≤ 1` have ranks 3 and 1 (`tri_rank_zero`); in degree 1 the structure maps
  `1 ≤ 2` and `2 ≤ 5` have ranks 0 and 1 (`tri_rank_one`).
- P2. `pathD` is the right-hand side of `path_reducerMatrix` of fixture R2 of
  [reducer order fixtures](#reducer-order-fixtures): the matrix with entries in rows 0 and 1 of
  column 2, for the reducer order A, C, AB with degrees 0, 0, 1 (`pathDegree`) and all grades 0
  (`pathGrade`). The pivot pair `(1, 2)` (`path_pivotPairs`) has equal grades and is dropped, so
  the only occurrence is the essential `⟨0, 0, .essential⟩` (`path_occurrences`); the degree-0
  diagram is `{(0, ⊤)}` and the degree-1 diagram is empty (`path_diagram`).
- P3. `sqD` is the right-hand side of `sqCert_reducerMatrix` of fixture R3: the matrix with the
  single entry in row 1 and column 2, with degrees and grades `0, 1, 2` (`sqDegree`,
  `sqGrade`). The occurrences are `[⟨1, 1, .finite 2⟩, ⟨0, 0, .essential⟩]`
  (`sq_occurrences`); the degree-1 diagram is `{(1, 2)}` and the degree-0 diagram `{(0, ⊤)}`
  (`sq_diagram`); in degree 1 the structure maps `1 ≤ 1` and `1 ≤ 2` have ranks 1 and 0
  (`sq_rank_one`).

The fixture file has 9 public definitions, all `def`s written out (`triD`, `triDegree`,
`triGrade`, `pathD`, `pathDegree`, `pathGrade`, `sqD`, `sqDegree`, `sqGrade`), and 17 public
theorems. Of the theorems:

- thirteen are a single `decide +kernel`: `tri_sq_zero`, `tri_strictBoundary`,
  `tri_lowersDegree`, `tri_pivotPairs`, `tri_essentialIndices`, `tri_occurrences`,
  `tri_diagram_zero`, `tri_diagram_one`, `path_pivotPairs`, `path_occurrences`,
  `path_diagram`, `sq_occurrences` and `sq_diagram`;
- `tri_monotone` unfolds `triGrade` by `simp only` and closes by `split_ifs <;> omega`;
- two rewrite twice with `rankOfStructureMap_eq_countP`, from `tri_sq_zero`,
  `tri_strictBoundary`, `tri_lowersDegree` and `tri_monotone`, and end in `decide +kernel`:
  `tri_rank_zero` and `tri_rank_one`;
- `sq_rank_one` proves three local hypotheses by `decide +kernel` and monotonicity by the term
  `Int.ofNat_le.mpr`, rewrites twice with `rankOfStructureMap_eq_countP` and ends in
  `decide +kernel`.

No fixture runs a certificate, evaluates `reducerDiagram` or mentions `dgm`.

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
| `Θ∂ + ∂Θ = I − φ_Q ∘ ψ_Q` (printed with `∂^Q` in the second term) | `one_sub_inclusion_mul_projection` |

MN's display in the proof of Lemma 2.5 prints the boundary generated by `κ_Q` in the term
`∂ ∘ Θ`. Since `Θ` maps into the chains of `X`, the identity holds only with the original
boundary `∂` there, which is the form `one_sub_inclusion_mul_projection` states.

The comparison mode is specialization in the unit: MN divide by the unit `κ(w(Q), Q)`, and
here it is specialised to `D a b = 1`. No rescaling by a general unit is provided. MN leave the
chain-map property of `ψ_Q` and `φ_Q` to the reader; here it is `projection_mul` and
`mul_inclusion`. The coefficient setting is an extension: the Lean statements need neither an
acyclic matching nor a principal ideal domain, and they hold over any commutative ring.

The proof of Prop. 4.4 (pp. 340–341) treats only `ψ_Q` and `φ_Q`: it shows that they are the
identity on the chains of the frames below the pair. `projection_gradeNonincreasing` and
`inclusion_gradeNonincreasing` specialise that filtration argument to one pair, with an integer
grade in place of MN's frame index `b`, and state grade-nonincreasingness rather than the
identity on lower frames. MN's Def. 4.1, which keeps each matched pair within one frame, is
background for the equal-grade hypothesis.

The grade theorems for `κ_Q` and `Θ` (`reducedDifferential_gradeNonincreasing`,
`homotopy_gradeNonincreasing`), `isFilteredDifferential_reduced`,
`isFilteredDifferential_boundary`, `GradeNonincreasing.mul`, the annihilation identities and
the unequal-grade fixture are library derivations attributed to no numbered result. See the
[MN13 source mapping](references.md#MN13).

`FilteredContraction`, its other operations, the `*_target` theorems, the vector identities,
`GradeNonincreasing.add` and the G1/G2 fixtures are library derivations attributed to no
numbered result; `ofUnitPair`
repackages the reduction step above and adds no source claim. `TauCeti.LinearSpecialContraction`,
recorded on #1074 against TauCeti commit `25bd01c`, is the closest notion to
`FilteredContraction`; TauCeti is not a dependency, and if it became one the comparison would
go through `Matrix.toLin'`.

The sublevel homology modules, `sublevelHomologyPModule`, the induced maps,
`sublevelHomologyEquiv`, `sublevelHomologyIso`, `finrank_sublevelHomology_eq` and the H1–H3
fixtures are library derivations attributed to no numbered result; MN13 Thm. 4.3 remains
background. `TauCeti.LinearContraction.homologyEquiv`, recorded on #1076 against TauCeti
commit `25bd01c`, is the closest ungraded, unfiltered analogue of `sublevelHomologyEquiv` at
one grade. It is stated for a single endomorphism `dM` of a module with the hypothesis
`dM ∘ₗ dM = 0`, and it runs in the opposite direction, induced by the inclusion. TauCeti is not
a dependency.

Each cancellation step of `FilteredContraction.ofSchedule` is `ofUnitPair`, transported and
restated by `cancelOn`, hence the reduction step mapped above, and adds no source claim; the
initial `toUniv` is only a restatement of the original complex. The schedule, the pivot
invariant `IsPivotSchedule` and its preservation, the Finset-carrier recursion, the composed
contraction `ofSchedule`, its characterizing facts and the H1, H2 and N fixtures of
`TDA.Persistence.Morse.IteratedCancellationExamples` are library derivations attributed to no
numbered result. No claim is made about how MN13 iterate the step in the proof of Thm. 2.4 or
in Thm. 4.3.

The cover lemmas, `schedule` and its lemmas, the arrow chain `rank_lt_of_boundary_ne_zero`,
the pivot theorem `isPivotSchedule_schedule`, the Morse complex of a certificate
(`mem_criticalSet_schedule`, `card_critical_schedule`, `morseDifferential`,
`isFilteredDifferential_morseDifferential`), its contraction `morseContraction`, its homology
isomorphism `morseHomologyIso` and the S1–S3 fixtures of
`TDA.Persistence.Morse.MatchingScheduleExamples` are library derivations attributed to no
numbered result. The order is derived from the rank certificate of #1039; MN's Def. 2.2
relation ◁ (`mnRel`) is related to it only by the unformalized remark in
[the pivot schedule of a certified matching](#the-pivot-schedule-of-a-certified-matching), and
no mapping to Def. 2.2 is added. `morseHomologyIso` is an isomorphism of grade-sublevel
homology of based complexes, not a statement about the persistent homology of the represented
complex; Thm. 4.3 remains background for #1041.

The support and cycle equivalences, `boundaryCycleCoordinates` and its lemmas, the simplicial
bridge `boundaryHomologyEquiv` and `boundaryHomologyIso`, the main theorem
`CertifiedMatching.morseSublevelModuleIso`, its corollaries and the M1–M7 fixtures of
`TDA.Persistence.Morse.SimplicialBridgeExamples` are library derivations attributed to no
numbered result. Thm. 4.3 remains background: the source was not re-read for
`TDA.Persistence.Morse.SimplicialBridge`, and no comparison of `morseSublevelModuleIso` with
Thm. 4.3 is recorded or made here.

`key`, the sort, `reducerEquiv`, `reducerMatrix` and its lemmas, `reducerContraction`,
`reducerHomologyIso` and the R1–R3 fixtures of `TDA.Persistence.Morse.ReducerOrderExamples` are
library derivations attributed to no numbered result; no source text is consulted.

The builders `reduced`, `pivotPairs`, `essentialIndices`, `pairOccurrence`, `occurrences` and
`diagram`, `stage` and its lemmas, `prefixHomologyEquiv` and its lemmas, the rank and
uniqueness theorems, the two instances, `TDA.Persistence.DiagramRankUniqueness` and the P1–P3
fixtures of `TDA.Persistence.Morse.ReducerDiagramExamples` are library derivations attributed
to no numbered result; no source text is consulted.

## What is not provided

- The simplicial bridge to `sublevelModule` and the main theorem of #1041 are in
  [the simplicial bridge and the Morse persistence theorem](#the-simplicial-bridge-and-the-morse-persistence-theorem);
  there is no interval decomposition of these persistence modules, and no agreement of a
  reducer run on the Morse complex of a certificate with `dgm` (#1061). The Morse complex
  of a certified matching and the derivation of its schedule are in
  [the pivot schedule of a certified matching](#the-pivot-schedule-of-a-certified-matching).
  The Morse differential is defined only by the recursion of
  `TDA.Persistence.Morse.IteratedCancellation`, and no gradient-path formula for it is
  provided.
- The reducer order of a filtered based complex, a grading-compatible `Equiv` of its
  generators to `Fin` along which a filtered differential over a field satisfies the reducer's
  input conditions, is in
  [the reducer order of a filtered based complex](#the-reducer-order-of-a-filtered-based-complex);
  the reducer output of a filtered based complex, its rank semantics and the uniqueness of a
  positive diagram with given slice counts are in
  [the graded reducer output and its rank semantics](#the-graded-reducer-output-and-its-rank-semantics);
  no certificate-level run on the Morse complex of a certified matching and no agreement of its
  output with `dgm` are provided (#1061).
- No matching check or search, no executable computation of `sublevelHomology`, and no
  runtime bound or speedup claim in these modules; no bridge from these based complexes or
  their sublevel homology to Mathlib `HomologicalComplex`, `Homotopy` or `HomotopyEquiv`, and
  no interval decomposition of `sublevelHomologyPModule`; for a filtered differential over a
  field, the positive diagram over `ℤ` with its ranks as slice counts is `reducerDiagram`, see
  [the graded reducer output and its rank semantics](#the-graded-reducer-output-and-its-rank-semantics).
