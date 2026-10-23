# Scalar PH loss derivatives

For the second-order extension, including nonlinear face curvature, see
[PH loss Hessians](sublevel-loss-hessians.md).

Fix a finite set of nonempty faces and a weak-order chamber for a family
of real filter functions. In degree `p`, the fixed face-order template has a
finite-birth and finite-death slot for each finite interval and a birth slot for
each essential interval. **All finite intervals remain in this template**, even
when their two values agree throughout the chamber. There is no real slot for
essential death at infinity.

`faceLossSlotFace` sends each slot to the face entering at its prefix index.
`faceLossSlotFace_injective` derives injectivity from the joint endpoint-count
theorem, including all three endpoint roles. This is a statement about face
indices, so equal grades cause no collision. `faceValueSelection` reads those
faces from the full face-value vector into ordered coordinates. It is a
continuous linear map of norm at most one for the finite-product maximum norms,
including empty products, and `fixedFaceLift_eq_selection` identifies it with
the existing diagram lift.

For a scalar loss `W` smooth through **every** ordered representative of the
base diagram, let `a_j` be its ordered-coordinate derivative at the unit vector
for slot `j`. Assign `β_s = a_j` when slot `j` selects face `s`, and `β_s = 0`
for unused faces. Injectivity makes this a single assignment. The theorem
`sublevelDiagramScalarLoss_hasFDerivAt` proves the genuine Fréchet derivative

\[
  D_x\bigl[W(\operatorname{dgm}_p(F(x)))\bigr]_{x_0}
    = \sum_{s\in\operatorname{TotalFace}(K)}
        \beta_s\,D_x[F(x)(s)]_{x_0}.
\]

The proof expands a continuous linear functional in the face-coordinate basis,
then uses the injective slot map to identify each basis image. The derivative
is a continuous **linear functional** on the normed parameter space. The
operator-norm bound is

\[
  \left\|D_x[W(\operatorname{dgm}_p(F(x)))]_{x_0}\right\|
    \leq \sum_s |\beta_s|\,\left\|D_x[F(x)(s)]_{x_0}\right\|.
\]

The scalar loss is `C¹` on an open neighborhood inside the given chamber.
`sublevelDiagramScalarLoss_derivative_independent` equates the resulting linear
functionals for compatible template choices, while
`sublevelDiagramScalarLoss_any_lifts_independent` covers any two admissible smooth
ordered lifts, including permutations of fixed occurrence labels. These facts
also equate their directional derivatives. They do not identify coefficient
vectors across presentations: dependent face-value derivatives can admit
different coefficient vectors for the same final functional.

## Concrete calculations

**Filled triangle, varying finite bar.** On the three-vertex filled triangle,
give vertices and two edges grade `0`, the last edge grade `t`, and the triangle
grade `2t`, with `t>0`. The first two edges form a tree; adding the last edge
creates the one-dimensional cycle. The triangle fills it. Thus the degree-one interval is `[t,2t)` and the signed finite
endpoint-difference loss is `2t-t=t`. Its birth slot selects the last edge and
has weight `−1`; its death slot selects the triangle and has weight `+1`.
Their face-value derivatives are `1` and `2`, so the derivative is
`(−1)·1+(+1)·2=1`. The shared prefix-index calculation is recorded in
[face-order-template.md](face-order-template.md), and triangle boundary
and cycle calculations are in
[simplicial-finite-homology.md](simplicial-finite-homology.md). The Lean theorem
`filled_triangle_H1_birth_and_death` supplies the corresponding simplex-attachment birth and death events. The interval and scalar arithmetic
in this paragraph are a mathematical calculation; they do not close the
separate original triangle-fixture acceptance tracked by #45.

**Persistent diagonal.** Give the same last edge and triangle grade `t>0`.
The prefix interval still has two endpoint slots, now `(t,t)`, while the degree-one diagram is empty because `orderedQ` discards a diagonal pair. The
signed loss has ambient ordered-coordinate weights `−1` and `+1` even at that
pair. The two face-value functions both have derivative `1`, and their
contributions cancel: `−1+1=0`. The Lean example
`moving_tied_edge_signed_loss_hasDerivAt` checks the same persistent-diagonal
phenomenon in a three-face edge filtration in degree zero. The generic
Lean examples `signed_finite_birth_slot_coefficient` and
`signed_finite_death_slot_coefficient` establish the nonzero ambient weights
for **every** finite slot, including a diagonal one.
`moving_tied_edge_has_finite_slot` proves that the tied edge has a retained
finite slot, and `moving_tied_edge_nonvacuous_cancellation` instantiates both
weights and their cancellation at that slot.

**Essential birth.** An isolated vertex with value `x` has degree-zero
diagram `{(x,∞)}`. The loss `essentialBirthSum` sums real essential births;
`essentialBirthSum_c1_all` checks smoothness through every representative,
including ones with diagonal finite pairs. The loss equals `x`, its
derivative is `1`, and `singleton_essential_face_coefficient` gives its sole
face coefficient `+1`. Infinity is never differentiated.

**Empty and unused.** `sublevelDiagramScalarLoss_empty_fderiv` gives zero for an empty
complex; the coordinate sum is empty. For any face not selected in the
fixed degree, `faceLossCoefficient_unused` gives coefficient zero. A permutation
of occurrence labels only changes the ordered presentation, so the generic
independence theorem leaves the derivative functional unchanged.
