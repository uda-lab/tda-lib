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
