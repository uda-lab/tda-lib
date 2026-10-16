# Real shifts and interleaving witnesses

An epsilon-interleaving compares two real-indexed modules by natural maps into
each other's shifts. Their two composites must equal the original modules'
structure maps across twice the shift. The API constructs the shifts and these
comparison maps from actual real parameters and structure maps.

## Modules, parameters and shifts

Fix a ring `R : Type u` and modules `M N : PModule.{u,0,w} R ℝ`. The coefficient
and module-carrier universes are independent. No finite-dimensionality,
constructibility or chosen decomposition is required. Parameters `ε δ : ℝ≥0`
are finite nonnegative real numbers; there is no shift by infinity.

`RealShift.translation ε` is the order homomorphism `t ↦ t+ε`.
`RealShift.shift ε` reindexes modules and natural transformations along it:

\[
(S_\varepsilon M)_t=M_{t+\varepsilon},\qquad
(S_\varepsilon f)_t=f_{t+\varepsilon}.
\]

The shifted structure map from `s` to `t` is the original map from `s+ε` to
`t+ε`. Thus positive shift moves an interval's support to the left.

The canonical `zeroIso M : S₀M ≅ M` and
`compIso ε δ M : Sε(SδM) ≅ S(ε+δ)M` apply `M` to the real-index equalities
`t+0=t` and `(t+ε)+δ=t+(ε+δ)`. They are natural in `M` and satisfy the unit
and associative coherence equations. Parameter equalities use `congrIso`;
the coherence statements display these transports explicitly.

## Transitions and the two witness equations

The transition `ηεM`, written `RealShift.transition ε M`, has component
the actual structure map `M[t≤t+ε]`. It is natural in the real index and
commutes with every module transformation. The zero transition is the inverse
of `zeroIso`; two transitions, followed by `compIso`, give `η(ε+δ)M`.

A value of `RealInterleaving ε M N` contains natural transformations

\[
f:M\longrightarrow S_\varepsilon N,\qquad
g:N\longrightarrow S_\varepsilon M
\]

and both identities

\[
\mu_M\circ S_\varepsilon(g)\circ f=\eta^{2\varepsilon}_M,\qquad
\mu_N\circ S_\varepsilon(f)\circ g=\eta^{2\varepsilon}_N,
\]

where `μ` is the constructed `compIso ε ε` and `2ε` means `ε+ε`.
At `t`, the first composite is `f_t` followed by `g_(t+ε)` and the transport
from `(t+ε)+ε` to `t+2ε`; it equals `M[t≤t+2ε]`. The other composite has the
same condition for `N`. `equations_iff` proves equivalence of the natural-
transformation equations and these component equations. `ofApp` accepts actual
natural maps and proofs of the component equations.

## Zero interleavings and the zero module

`RealInterleaving.symm` exchanges the maps; `refl` uses the actual transitions.
`zeroEquivIso` gives an equivalence between zero-interleaving witnesses and
natural isomorphisms. Its two conversions are inverse, using the constructed
unit and composition coherences.

For the zero functor, `nonempty_zero_iff` proves

\[
\operatorname{Nonempty}(\operatorname{RealInterleaving}_\varepsilon(M,0))
\quad\Longleftrightarrow\quad \eta^{2\varepsilon}_M=0.
\]

In one direction the maps to and from the shifted zero module are zero, so the
witness equation forces annihilation. In the other direction the zero maps
construct the witness. This criterion uses the actual structure map.

The checked interval examples use the existing field-valued
`RealBarcode.intervalModule`. At `ε=1`, `[0,2)` interleaves with zero: exact
death is excluded, so its double-shift maps vanish. At `ε=1`, `[0,3)` does
not: the map from parameter `0` to `2` preserves coefficient `1`.
The essential interval `[0,∞)` fails the criterion at every finite `ε`, because
the map from `0` to `2ε` preserves `1`. A field has `1≠0`; this nontriviality
is needed for the negative examples. The basic ring-valued API does not impose it.

## Source and scope

[Bauer--Lesnick, arXiv:1311.3681v4](https://arxiv.org/html/1311.3681v4), §3.1,
defines the field-valued shift, transition and interleaving with these conventions.
The ring-valued constructions, explicit coherence and zero-module criterion are
proved library extensions and consequences. Source manifestation and rights
metadata are recorded in [BL15-v4](references.md#BL15-v4).

This API provides concrete witnesses. Interleaving composition and enlargement,
generic flows, interleaving distance and its infimum/infinity/attainment laws,
both isometry inequalities and the interleaving-to-matching direction are separate
work. The [matching-to-interleaving construction](matching-interleavings.md) supplies
concrete witnesses for finite positive barcode realizations. The finite-constructible
[barcode realization](real-barcode-realization.md)
supplies a different natural isomorphism; no such decomposition is an input here.
