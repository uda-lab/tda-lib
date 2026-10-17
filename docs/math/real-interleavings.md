# Real interleavings and their extended distance

An epsilon-interleaving compares two real-indexed modules by natural maps into
each other's shifts. Their two composites must equal the original modules'
structure maps across twice the shift. The API constructs the shifts and these
comparison maps from actual real parameters and structure maps. Taking the infimum
of all admissible finite parameters gives an extended pseudometric, with no
assumption that the infimum is attained.

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

## Enlargement, composition and isomorphism transport

For `ε ≤ δ`, `RealShift.shiftLE` has components `M[t+ε≤t+δ]`.
`RealInterleaving.mono` postcomposes both comparison maps with these
structure maps, producing a δ-interleaving.

Given an ε-interleaving between `M,N` and a δ-interleaving between `N,P`,
`RealInterleaving.trans` gives an `(ε+δ)`-interleaving between `M,P`.
Its forward map is

\[
M\longrightarrow S_\varepsilon N
 \longrightarrow S_\varepsilon S_\delta P
 \longrightarrow S_{\varepsilon+\delta}P.
\]

The reverse map uses the comparisons in reverse order and the canonical
identification of `δ+ε` with `ε+δ`. Naturality moves the intermediate
structure maps past the comparisons; the original two witness equations then
give both double-shift equations for the sum.

`RealInterleaving.congr` transports both modules along natural isomorphisms,
conjugating the comparison maps without changing the parameter.

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

The [kernel and cokernel shortness results](real-interleaving-shortness.md)
prove that either interleaving morphism has actual defects with zero
double-shift transitions. They use the witness equations and naturality of
the actual kernel inclusion and cokernel projection, over the same rings.

## Distance, infinity and approximation

`realInterleavingDistance M N : ℝ≥0∞` is

\[
d_I(M,N)=\inf\{\varepsilon\in\mathbb R_{\ge0}\mid
  \operatorname{Nonempty}(\operatorname{RealInterleaving}_\varepsilon(M,N))\}.
\]

The empty infimum is infinity. Thus `d_I=⊤` holds exactly when there is no
finite-parameter interleaving; an essential interval and zero give such a pair.
Every ε-witness gives `d_I≤ε`. For any extended bound `r : ℝ≥0∞`,

\[
d_I(M,N)<r\quad\Longleftrightarrow\quad
\exists\varepsilon\in\mathbb R_{\ge0},\quad
\varepsilon<r\ \text{and an ε-interleaving exists}.
\]

At `r=0` both sides are false; at `r=⊤` this is existence of a finite witness.
The weak bound `d_I≤ε` alone does not supply an ε-witness.

The distance is symmetric, is zero on the diagonal, is invariant under natural
isomorphism in each argument, and satisfies

\[
d_I(M,P)\le d_I(M,N)+d_I(N,P).
\]

This includes infinite summands. The proof bounds the distance by `ε+δ` for
every pair of witnesses and distributes ENNReal addition over their infima;
it requires neither an optimal parameter nor a nonempty witness set.

Zero distance is equivalent to interleavings at **every** positive finite
parameter. It need not give a zero-interleaving or a natural isomorphism.
The explicit ephemeral example over ℚ has fiber ℚ at time zero and zero
elsewhere. Its maps are identity when both indices are zero and zero otherwise;
ordered intermediate indices ensure the functor composition law. Every positive
double-shift map is zero, while the time-zero fiber is nonzero. It therefore has
distance zero from the zero module with no zero-interleaving: this infimum is
not attained. The distance API is a plain function with extended pseudometric
laws, without a separation or attainment assertion.

## Positive scaling

For `c : ℝ` with `hc : 0 < c`, `PModule.scale c hc M` reindexes `M` along
`t ↦ c⁻¹ * t`, so its value at `t` is `M.obj (c⁻¹ * t)`. This direction agrees
with `FilterFunction.scale` and `scale_sublevel`, and with `Diagram.scale`: a
bar `[b, d)` becomes `[c b, c d)`.

Scaling and shifting commute through `PModule.scaleShiftIso`. Its component is
the transport induced by

\[
c^{-1}(t+c\varepsilon)=c^{-1}t+\varepsilon.
\]

Consequently, `RealInterleaving.scale` sends an ε-interleaving to a
`Real.toNNReal c * ε`-interleaving of the scaled modules, and
`nonempty_realInterleaving_scale_iff` gives the converse witness equivalence.
The exact distance law is

\[
d_I(PModule.scale\ c\ hc\ M,PModule.scale\ c\ hc\ N)
=\operatorname{ENNReal.ofReal}(c)\,d_I(M,N),
\]

as stated by `realInterleavingDistance_scale`. It holds over every ring, with
no constructibility or finite-dimensionality hypothesis, and includes infinite
distance: `realInterleavingDistance_scale_eq_top_iff` preserves the value `⊤`.
The hypothesis `0 < c` is essential. A negative factor is not monotone, while
the factor `0` gives a constant reindexing; for the essential infinite-distance
case its left-hand distance is `⊤` but the proposed right-hand side is
`0 * ⊤ = 0`.

### Constructible and sublevel bridge

For a finite critical grid, `FiniteConstructible.scaleGrid` and
`FiniteConstructible.IsConstructible.scale` transport constructibility to the
scaled module. `FiniteConstructible.moduleDiagram_scale` says that the diagram
on the scaled grid is `Diagram.scale` of the original diagram, paralleling the
[shift diagram formula](constructible-shift-diagrams.md); the bottleneck form
`FiniteConstructible.bottleneck_moduleDiagram_scale` is the corresponding
[finite-constructible isometry route](constructible-isometry.md).

At the filtration level, `sublevelModule_scale` is an equality, and
`realInterleavingDistance_sublevelModule_scale` gives the same exact distance
law over any ring. Finally, `moduleDiagram_sublevelModule_scale` agrees with
`dgm_scale`, so filter scaling and module scaling produce the same diagram.

## Source and scope

[Bauer--Lesnick, arXiv:1311.3681v4](https://arxiv.org/html/1311.3681v4), §3.1,
defines the field-valued shift, transition, interleaving and distance with these
conventions; Remark 3.1 supplies enlargement and additive composition.
Positive scaling and its exact interleaving-distance law are library extensions
of BL15-v4 §3.1, not theorems of that source.
The ring-valued constructions, explicit coherence and zero-module criterion are
proved library extensions and consequences. The unconditional ENNReal triangle
also includes infinite summands, where the inequality is automatic.
Source manifestation and rights
metadata are recorded in [BL15-v4](references.md#BL15-v4).

Concrete witnesses from inclusions of simplicial filtrations, including the
log-scale Čech–Rips interleaving, are constructed in
[inclusion interleavings](cech-rips-interleaving.md).

Generic flows remain separate. The
[matching-to-interleaving construction](matching-interleavings.md) supplies
concrete witnesses and `d_I≤d_B` for finite positive barcode realizations,
transported to finite-constructible modules by the actual
[barcode realization](real-barcode-realization.md) isomorphism. The
[finite-constructible isometry](constructible-isometry.md) constructs the
opposite cost-bounded matching and proves extended-distance equality and
finite-parameter witness equivalence. Its field, critical-fiber finiteness,
zero-left and half-open assumptions restrict that theorem's domain; no such
decomposition or isometry hypothesis is an input to the general distance API.
