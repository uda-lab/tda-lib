# Scalar calculus through ordered diagram presentations

The [second-order extension](actual-ph-loss-hessians.md) establishes C² scalar
regularity and genuine second derivatives, retaining both terms of the
ordinary second-order chain rule.

`DiagramCoordinates m n` is `(Fin m → ℝ × ℝ) × (Fin n → ℝ)`, the full domain of
`orderedQ`. A finite pair may be reversed or diagonal; `orderedQ` retains a
reversed pair and deletes a diagonal pair. Essential points have only a birth
coordinate. The blocks can be empty independently.

`LocalDiagramLift B m n` gives an open set `U`, a coordinate map `l` that is
`C¹` on `U`, and the equality `B y = orderedQ m n (l y)` for every `y ∈ U`.
`C1ThroughAllRepresentatives V D` requires a `C¹` pullback of `V` near **each**
coordinate representative of `D`, for every `m,n`. The neighborhood may vary
with the representative.

If `x ∈ U` and `V` satisfies that condition at `B x`, the scalar map `V ∘ B`
is `C¹` on a smaller open neighborhood of `x`. It has the ordinary Fréchet
derivative

`D(V ∘ B)(x) = D(V ∘ orderedQ m n)(l x) ∘ Dl(x)`.

Two local lifts of the same `B` give the same composed derivative, even with
different numbers of finite and essential coordinates. This follows by
uniqueness of the derivative of `V ∘ B`; their coordinate derivatives are not
compared. These are statements about scalar maps on normed spaces. They do not
define a derivative or topology on `Diagram`, and do not assert that an actual
persistent homology map admits such a lift.

The signed finite endpoint-difference loss assigns `d - b` to a finite pair
and zero to an essential point. Its pullback through every `orderedQ` is the
linear sum of the listed endpoint differences. This includes diagonal pairs
because they contribute zero, and reversed pairs because the loss is signed.
For one pair the birth and death derivative weights are `-1` and `+1`.

The absolute finite endpoint-difference loss fails the all-representatives
condition at the empty diagram: the zero-coordinate presentation is constant,
but the diagonal one-pair presentation `(0,t)` pulls the loss back to `|t|`.
The formal examples also show that an essential-only presentation and a
finite-only presentation can vary, while the zero-coordinate presentation and
any fixed ordered representative give constant lifts.

## Correspondence with ordered-barcode calculus

[Leygonie–Oudot–Tillmann, accepted version, Definitions 2.8 and 3.1](https://arxiv.org/pdf/1910.00960v4)
uses the full ordered coordinate space, including reversed finite pairs and
redundant diagonal coordinates. `Diagram` stores only its off-diagonal
multiset; deleting diagonal coordinates in `orderedQ` represents the
source's implicitly repeated diagonal. The library's finite-product
maximum norm and the source's Euclidean norm give the same smooth structure
on each fixed finite coordinate space.

`DiagramContDiffAt` and `CrThroughAllRepresentatives` retain the local
factorization and universal representative quantifiers of source
Definitions 3.3 and 3.10. `localLift_scalar_cr` and the derivative theorems
recover Proposition 3.14 for scalar losses and real normed parameter spaces.
Finite-dimensional real parameter spaces give the source specialization;
the library also permits general normed parameter spaces with the stated
lifts and regularity assumptions. General smooth manifolds and their
charts are not formalized here. The index `ω` applies mathlib's regularity
predicate to the coordinate map; no separate barcode analyticity
equivalence is asserted.

`ActualDiagramRegularity` supplies both the full-template lift and the
occurrence-preserving strict lift on the original open ordering-equivalent
neighborhood. The strict lift deletes the persistently diagonal pairs,
recovering Theorem 4.7 and Proposition 4.14. The present local-lift API
requires ordering equivalence, even though the underlying template
evaluation theorem only needs a common compatible enumeration. Scalar
regularity may shrink the neighborhood, while both lifts' factorizations
remain on their stated carriers.

The face derivative coefficients and Hessian entries depend on the chosen
ordered presentation. The composed scalar derivatives agree by uniqueness.
The second-order face formula is a library consequence of the ordinary
second-order chain rule: it keeps both the loss-Hessian pullback and the
loss-gradient applied to face-value curvature. It is not an additional
Hessian theorem claimed from Theorem 4.7. Diagonal restriction explains
cancellation of persistent ties without forcing their ambient coefficient
entries to vanish.
