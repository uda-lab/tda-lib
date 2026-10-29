# Positive affine slices of persistence modules

Let $n\ge1$ and choose vectors $a,b\in\mathbb R^n$ with $a_i>0$ in
every coordinate. The affine line

$$L(t)_i=b_i+t a_i$$

is monotone for the coordinatewise order. Restricting a persistence module
$M$ along this line gives the real-indexed module $t\mapsto M(L(t))$,
with the original structure maps between these parameters.

The entrance time of a grade $p$ is

$$\tau_L(p)=\max_i\frac{p_i-b_i}{a_i}.$$

It satisfies the exact equivalence

$$\tau_L(p)\le t\quad\Longleftrightarrow\quad p\le L(t).$$

`PositiveAffineLine` stores the offset, slope and coordinate positivity;
`entrance_le_iff` proves this equivalence. It is a Galois connection:
entrance time is left adjoint to the line parameterization. Its minimum
slope $w=\min_i a_i$ is positive, and

$$L(t)+\varepsilon\mathbf 1\le L(t+\varepsilon/w)\qquad(\varepsilon\ge0).$$

This inequality provides the additional structure maps needed when comparing
coordinate shifts with shifts along a line of unequal slopes.

## Restricting finite presentations

Over an arbitrary coefficient ring, a finite graded-free presentation of
$M$ gives a finite graded-free presentation of its restriction. Each
generator born at $p$ is regraded to $\tau_L(p)$, and each relation is
regraded in the same way. Their occurrence sets stay unchanged.

The entrance-time equivalence identifies the supported free fibers at each
parameter, retaining every coefficient. These identifications commute with
the structure maps. Conjugating the restricted relation map gives the new
relation map, and precomposition preserves its cokernel. Thus the presented
module is naturally isomorphic to the actual restriction of $M$.

`GradedFree.finitelyPresented_reindex_of_galoisConnection` proves the general
right-adjoint reindexing result. `PositiveAffineLine.finitelyPresented_slice`
applies it to a positive affine line. The companion
`finitelyPresented_fromReal_slice` supplies the original presentation
predicate in the one-coordinate form used by the ordinary barcode API.
The generator-carrier universe is retained; arbitrary-field consumers can
use the existing small-presentation convention.

The nonempty coordinate set and strictly positive slopes are essential.
For zero coordinates, a nonzero module on the singleton parameter space
restricts to a constant module on all of $\mathbb R$, which has no finite
set of real birth grades generating it. General monotone reindexing does
not supply the entrance-time adjunction.

## Hook intervals and multiplicity

Over a field, a finite hook with birth $p$ and death $q$ has support
$\{x:p\le x,\ q\nleq x\}$. Its restriction therefore has support

$$[\tau_L(p),\tau_L(q)).$$

`finiteHook_reindex_eq` identifies the actual restricted module with this
interval module. Both endpoints use a maximum of normalized coordinate
differences. A principal hook supported on $\{x:p\le x\}$ restricts to
$[\tau_L(p),\infty)$; `principalHook_reindexIso` gives the natural comparison.

Even when $p<q$ in the coordinatewise partial order, the two entrance times
can coincide. For example, $p=(0,1)$ and $q=(1,1)$ give a nonzero hook whose
restriction to $L(t)=(t,t)$ is zero. `hookEndpoints` omits such finite
intervals and retains every principal interval with infinite death.
`sliceHookMultiset` applies this operation to occurrences, so different
hooks with the same retained endpoints contribute their full multiplicity.
Its count formula makes these collisions explicit.

The support formulas and finite-presentation construction above are direct
library derivations. [Botnan, Oppermann and Oudot, §5.3, Corollaries 5.8–5.9](https://arxiv.org/html/2107.06800v3#S5.SS3)
describe restriction and cancellation for signed rank decompositions;
Corollary 5.8 is stated for rectangles. Hooks use the support computation
above, and their death formula differs from the rectangle formula. This
page establishes the slice presentations and individual hook comparisons;
it makes no cancellation or matching-distance claim.
