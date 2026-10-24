# Join-indexed resolutions of generated upsets

Let `k` be a field, `P` a lattice, and `f : Fin m → P` a finite indexed family. Its generated
upset is

`U = {p : P | ∃ i, f i ≤ p}`.

For each nonempty set of occurrences `A ⊆ Fin m`, write `j_A` for the join of the values `f i`
with `i ∈ A`. The corresponding summand is the principal-upset module born at `j_A`. In degree
`r`, `TDA.Persistence.GeneratedUpsetResolution.term f r` is the finite biproduct of these
modules over the faces with `r+1` occurrences. The differential deletes each occurrence in
increasing `Fin m` order, with the alternating sign, and maps the face module into the module
of the smaller face. The augmentation maps degree zero into the support-interval module on
`U`.

The construction preserves occurrences: if two values of `f` are equal, their singleton faces
and the higher faces containing them remain distinct summands. Each term is projective because
it is isomorphic to the graded-free module on its face generators, and each principal-upset
module is projective.

At an index `p`, the active occurrences are `i` with `f i ≤ p`. The summands visible at `p`
are exactly the nonempty faces of the active-occurrence simplex. The equivalence
`termEvaluationEquiv` identifies the evaluated terms with its simplicial chains, sends the
actual differential to the signed simplicial boundary, and identifies augmentation with the
sum of degree-zero coefficients. If the active set is nonempty, coning by any active vertex
contracts the simplex chain complex, including its augmentation. If the active set is empty,
the evaluated face terms and the support-module fiber are all zero. Thus
`resolution_pointwise_exact_at` gives surjectivity and exactness at every term, while
`differential_comp_differential` and `differential_comp_augmentation` establish the chain laws.

The separate empty-family result is `generatedSupport_fin_zero_module_isZero`: when `m = 0`,
the generated support and its support module are zero, and every face-sum term is zero by
`term_fin_zero_eq_zero`.

These are ordinary projective resolutions for arbitrary lattices and finite indexed families;
no finiteness or decidability condition on the order is needed. This statement does not assert
that the resolution is shortest or minimal, nor does it claim a global-dimension bound.

The construction formalizes Botnan, Oppermann, Oudot and Scoccola,
[*On the bottleneck stability of rank decompositions of multi-parameter persistence modules*,
arXiv:2208.00300v3, Proposition 5.1](https://arxiv.org/html/2208.00300v3#S5.SS1). The Lean interface is
in [`GeneratedUpsetResolution.lean`](../../TDA/Persistence/GeneratedUpsetResolution.lean); focused
fixtures are in [`GeneratedUpsetResolutionExamples.lean`](../../TDA/Persistence/GeneratedUpsetResolutionExamples.lean).
