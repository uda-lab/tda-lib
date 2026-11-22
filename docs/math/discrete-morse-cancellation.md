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
This is the regression data for a later reducer adapter (#1061); this unit sorts nothing.

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
avoids nested survivors by running each step on a Finset-indexed carrier. `TDA.Persistence.Morse.FilteredContraction` formalises no homology; the
section
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
[based complexes and the column convention](#based-complexes-and-the-column-convention): `D r c` is the coefficient of
`r` in `d c`. `scheduleEndpoints l` lists the `2·|l|` endpoints in order; its body is that of
`MatchingInput.endpoints`. `IsPivotSchedule grade D l` is the conjunction of three conditions:

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
`FiniteInput.boundary`, suppose `D (a i) (b j) ≠ 0` with `i ≠ j`. If `a i` is a
codimension-one face of `b j`, the cover `(a i, b j)` is not a matched pair, since the
endpoints are distinct, so the arrows `a j → b j → a i` give `rank (a j) < rank (a i)`. Listing
the pairs in increasing rank of the lower face therefore gives a pivot schedule. This
derivation is not formalized here: that nonzero boundary entries are covers, and the sorting
itself, are left to unit 3 of #1041. Here the order is supplied, and fixture H1 in
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
- any derivation of a schedule from an acyclic matching or a #1039 `CertifiedMatching`
  (unit 3 of #1041);
- any homology or persistence statement; the simplicial bridge and the main theorem of #1041
  are unit 5 of #1041.

### Schedule fixtures

The fixtures are in `TDA.Persistence.Morse.IteratedCancellationExamples`, over `ZMod 2`. Every
closed computation is `decide +kernel`. `square_boundary` and `circle_boundary` first unfold
the boundary with `norm_num`, as `triangle_boundary` of `TDA.Persistence.Morse.UnitCancellationExamples` does,
because `FiniteInput.boundary`
does not reduce in the kernel.

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
  `cyclicPairs`, for which the checker of #1039 accepts no rank (`cyclic_no_certificate`). `cyclicOrders`
  lists six distinct permutations of `cyclicPairs` (`cyclicOrders_perm`), and none of them is
  a pivot schedule (`cyclic_not_isPivotSchedule`). `D C AC = 1`, but after cancelling (A, AB)
  and then (B, BC) head first, the entry at (C, AC) is 0 (`cyclic_pivot_destroyed`), so the
  third pair can no longer be cancelled.

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

Each step of `FilteredContraction.ofSchedule` is `ofUnitPair`, transported and restated by
`cancelOn`, hence the reduction step mapped above, and adds no source claim. The schedule, the pivot invariant `IsPivotSchedule` and its
preservation, the Finset-carrier recursion, the composed contraction `ofSchedule`, its
characterizing facts and the H1, H2 and N fixtures of
`TDA.Persistence.Morse.IteratedCancellationExamples` are library derivations attributed to no
numbered result. No claim is made about how MN13 iterate the step in the proof of Thm. 2.4 or
in Thm. 4.3.

## What is not provided

- No Morse complex of a matching, no derivation of a cancellation schedule from a #1039
  `CertifiedMatching` (unit 3 of #1041), and no simplicial bridge from
  `sublevelHomologyPModule` to `sublevelModule` or `simplicialHomologyPModule`; these are
  #1041.
- No reducer adapter, no chosen ordering or Equiv of survivors to `Fin`, and no
  grading-compatible ordering; these are #1061. `FilteredContraction.reindex` transports a
  contraction along such an Equiv once one is given.
- No matching check or search, no executable computation of `sublevelHomology`, and no
  runtime bound or speedup claim in these modules; no bridge from these based complexes or
  their sublevel homology to Mathlib `HomologicalComplex`, `Homotopy` or `HomotopyEquiv`, and
  no barcode or interval decomposition of `sublevelHomologyPModule`.
