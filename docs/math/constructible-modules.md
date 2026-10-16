# Reconstructing a real module from finite strata

`TDA.Persistence.FiniteConstructible` reconstructs a real-indexed persistence module
from finitely many critical samples. The coefficient ring and module-carrier universes
are independent. Reconstruction requires neither a field nor finite-dimensional fibers.

## Strata and samples

Fix a ring `R`, a module `M : PModule.{u,0,w} R ℝ`, and a strictly increasing list of
critical values, bundled as `c : Fin n ↪o ℝ`. The monotone map

\[
q(t)=\#\{i\mid c_i\le t\}\;\in\;\operatorname{Fin}(n+1)
\]

is `cellIndex c`. The zero cell is the ray before all critical values. Cell `i+1`
contains `[c_i,c_{i+1})` when a next critical value exists, and the final cell is
`[c_{n-1},∞)`. In particular, `q(c_i)=i+1`: a critical endpoint belongs to the new
cell. With `n=0`, every parameter belongs to cell zero.

`sample c M` is a finite module `A` with an actual zero object at index zero and
`A(i+1)=M(c_i)`. Its positive structure maps are the original maps between critical
parameters; maps from the initial zero object are zero. This initial stage has no
real critical value and must not be passed to an endpoint adapter as an extra grade.

## Hypotheses and natural isomorphism

`IsConstructible c M` requires two properties:

- `M(t)` is a zero object whenever `t` lies below every critical value.
- Whenever `s≤t` and `q(s)=q(t)`, the actual structure map `M(s)→M(t)` is an
  isomorphism.

These conditions concern the module's fibers and maps. They assume no finite
factorization, chosen bases, rank equality or reconstruction isomorphism. For an empty
critical list, the predicate is equivalent to every fiber being zero. A finite module
with zero initial fiber satisfies the predicate after reindexing along `q`.

`reconstructionIso c M hM` constructs

\[
q^*A\;\cong\;M.
\]

On a positive cell its forward component is the actual map `M(c_i)→M(t)`, with the
sample fiber identified by its cell index. On the left cell it is the map from the
zero object. Naturality is proved before invertibility: for positive source and target
cells, both sides of the square are the same composite `M(c_i)→M(t)`; for a zero
source, uniqueness of maps from a zero object gives the square. Constructibility then
makes each component invertible. Mathlib's componentwise natural-isomorphism
construction supplies the inverse transformation and its naturality, together with
both inverse identities. The API exposes both structure-map naturality equations and
both identities explicitly.

The final tail may remain nonzero. Its maps need only be isomorphisms, and the
reconstruction does not force them to be identities. The examples include a nonzero
step module with a change of coordinates by a factor of two within its single final
cell, as well as empty, left-ray and exact-critical-value cases.

## Barcode and source boundary

Applying the existing finite decomposition to `A` additionally requires a field
`k : Type u`, carrier universe `u`, and finite-dimensional critical fibers; the zero
initial fiber supplies the remaining sampled finiteness. These conditions belong to
`barcodeRealizationIso`, separately from reconstruction. That consumer constructs a
natural isomorphism to real half-open interval modules with the existing diagram
endpoints. See [real barcode realization](real-barcode-realization.md).

[Bauer--Lesnick, arXiv:1311.3681v4](https://arxiv.org/html/1311.3681v4), §2.1,
provides the functor, natural-transformation and interval-module semantics. Section 2.3
distinguishes endpoint decorations. The reconstruction here is a library construction
with an explicit left-zero, left-closed/right-open convention, rather than a literal
translation of a numbered theorem. Its source manifestation and rights metadata are
registered in [BL15-v4](references.md#BL15-v4).

The paper's isometry theorem (Theorem 3.5), algebraic stability direction (Theorem 6.4)
and converse direction (Theorem 8.2) are outside this reconstruction API. It defines no
PH interleaving distance and proves neither inequality. Arbitrary decorated endpoints,
nonzero left tails and infinite/q-tame decomposition are also outside its contract.
