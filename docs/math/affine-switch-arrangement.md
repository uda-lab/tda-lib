# Finite affine cuts for endpoint costs

This construction supplies a finite arrangement on which every endpoint-cost
comparison has a constant sign. Its inputs are a finite set of points in
`ℝ × ℝ`; it has no persistence-module or barcode hypothesis. The main result is
`AffineSwitch.SameCell.sign_cost_sub_eq`, with order and equality forms
`SameCell.cost_le_iff` and `SameCell.cost_eq_iff`.

## Coordinates and costs

Represent a line by `y = m x + c`, with `m > 0`. For a point `s = (s₁,s₂)`, set

\[
H_s(m,c)=\max(ms_1,s_2-c),\qquad
C_{u,v,\delta}(m,c)=\frac{|H_u(m,c)-H_v(m,c)|}{\delta\max(1,m)}.
\]

`push` and `cost` implement these expressions. The denominator parameter is
`1` for a pair cost or `2` for a diagonal cost. `denominator false = 1` and
`denominator true = 2`; `exists_denominator_iff` characterizes these choices.
The common factor `max(1,m)` is strictly positive. When `m ≤ 1` the cost is
`|H_u-H_v|/δ`; when `1 ≤ m` it is `|H_u-H_v|/(δ*m)`. Both formulas agree at
`m = 1`. The algebraic definitions and comparison theorem also make sense on
the full parameter plane, although only positive slopes describe the intended
slice geometry.

## The finite family

`Form` stores coefficients `(A,B,C)` and evaluates to `A*m+B*c+C`. For a finite
set `S`, `cuts S` contains:

- The branch cut `s₁*m+c-s₂` for every `s ∈ S`.
- The normalization cut `m-1`.
- Both signed comparison forms for every ordered quadruple `(u,v,w,x)` from
  `S`, every choice of one of the two affine expressions for each endpoint,
  and every `δ,η ∈ {1,2}`:
  \[
  \eta(h_u-h_v)-\delta(h_w-h_x),\qquad
  \eta(h_u-h_v)+\delta(h_w-h_x).
  \]

`SwitchIndex S` enumerates the choices as finite data. Repeated points are
allowed, and a finite image collects the resulting forms. No orientation of
the endpoint differences is prescribed. Zero forms are retained:
`zero_mem_cuts` derives one from repeated endpoints whenever `S` is nonempty.
`Form.eval_eq_zero_iff` characterizes identically zero forms by their three
zero coefficients.

A sign profile records the negative, zero or positive sign of every cut.
`SameCell S p q` means equality of those profiles. `finite_signProfiles` shows
that only finitely many profiles are realized. These cells include boundary
strata and equalities; no generic-position assumption excludes them.

## Why the comparison sign is invariant

First, the sign of `s₁*m+c-s₂` determines which expression realizes `H_s`.
At equality both expressions agree, and `active` consistently selects the
first. Thus `SameCell.active_eq` obtains the same branch at two parameters
in one cell.

For real numbers `a,b` and positive `δ,η`, cross multiplication and comparison
of squares give

\[
\operatorname{sign}\left(\frac{|a|}{\delta}-\frac{|b|}{\eta}\right)
=\operatorname{sign}\bigl((\eta a-\delta b)(\eta a+\delta b)\bigr).
\]

`EndpointCost.sign_abs_div_sub_eq_sign_factors` proves this identity, including
zero inputs. A common positive divisor preserves the sign. After selecting
the active branches, both factors on the right are members of `cuts S`.
Their signs agree at two parameters in the same cell, so their product signs
agree. This proves the endpoint-cost conclusion from the finite input and
its affine sign profile. Comparison invariance is never an input assumption.

The coefficient representation also distinguishes elementary geometric cases.
If `B ≠ 0`, the cut vanishes precisely on lines through
`(A/B,-C/B)`. If `B = 0` and `A ≠ 0`, it prescribes slope `-C/A`, which meets
the positive-slope domain only when that value is positive. If both `A` and
`B` vanish, the form is constant. These interpretations require no division
by a zero coefficient and are not used to build a projective-space API.

## Why both factors matter

Take `u=(0,3)`, `v=(3,0)`, `w=(0,4)`, `x=(5,4)`, `δ=1` and `η=2`.
Along `m=1`, `-1<c<3`, the four push branches are fixed, but the cost
difference is

\[
|c|-\frac{1+c}{2}.
\]

It vanishes at `c=-1/3` and `c=1`, but not at `c=0`. The regression module
proves this and shows that no single affine equation in `c` describes those
equalities throughout the interval. The two signed factors on the fixed
branches are `2-c-m` and `10-3c-11m`. Their proper-point interpretations are
the two pencils through `(1,2)` and `(11/3,10/3)`.

This tests the fixed-push, single-pencil formulation in Bapat et al.,
[Lemma 4.2](https://arxiv.org/html/2210.12868v3#S4). It does not refute that
paper's finite-switch-set or finite-maximum results: collecting all ordered
quadruples and mirrored formulas may retain the needed cuts. The present
proof explicitly collects both factors and is independently derived.

## Scope and sources

Bapat et al., [arXiv:2210.12868v3](https://arxiv.org/html/2210.12868v3),
Theorems 3.1 and 4.4, motivate the eventual matching-distance goal.
Kerber–Lesnick–Oudot, [arXiv:1812.09085v2](https://arxiv.org/html/1812.09085v2),
§4, supplies related arrangement context. The result here is the endpoint
comparison prerequisite, not a formalization of either paper's main theorem.

Transport of barcode occurrences, essential endpoints, horizontal or vertical
limits, dominance of those limits, and maximum attainment remain separate.
The real-coordinate construction is noncomputable Lean theory. It does not
provide an executable exact matching-distance algorithm or a complexity bound.
