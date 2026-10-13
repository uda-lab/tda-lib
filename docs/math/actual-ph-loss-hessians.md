# Second derivatives of actual scalar PH losses

Let `K` have finitely many actual nonempty faces, and let `F` be a family of real
filter functions on a real normed parameter space. On an open set `U`, assume
each face value is `C²` and the complete weak ordering of face values agrees
with that at `x₀ ∈ U`. Neither a finite ambient vertex type nor an inner product
on the parameter space is needed.

The fixed full-template lift `L` is `C²` on the same `U` and represents the
actual sublevel diagram throughout `U`. It is the composite `R ∘ G`, where `G`
collects all face values and `R = faceValueSelection` is fixed and continuous
linear. Thus both derivatives select the corresponding face derivatives;
there is no differentiation of a changing sort or pairing.

`C2ThroughAllRepresentatives V D₀` requires the pullback of `V` to be `C²` near
every ordered representative of `D₀`, for every pair of coordinate counts.
The domain includes reversed and diagonal finite pairs. At `z = L(x₀)`, write
`φ = V ∘ orderedQ`. The coordinate neighborhood supplied by this condition
may shrink the scalar neighborhood: the actual scalar function
`ℓ(x) = V(dgmₚ(F(x)))` is `C²` on an open `W` with `x₀ ∈ W ⊆ U`.

## Face formula

Use the convention `D²f(x)[h,k] = D(Df)(x)[h][k]`. The second derivative is a
continuous bilinear map, represented in Lean by a curried continuous linear
map. Let `uⱼ` be the existing coordinate units and `s(j)` the existing injective
slot-to-face assignment. Keep `β` from `faceLossCoefficient` and define

\[
\Gamma_{\sigma\tau}
 = D^2\varphi(z)[R e_\sigma,R e_\tau],
\]

where `eσ` is a unit in the complete face-value space. This equals
`D²φ(z)[uⱼ,uₗ]` for `σ = s(j)` and `τ = s(l)`; an unused face gives a zero row
and column. The corresponding first-order evaluation is the existing `βσ`.

The bilinear form `actualFaceLossHessian` is

\[
B[h,k] = \sum_\sigma\sum_\tau
  \Gamma_{\sigma\tau}\,DF_\sigma(x_0)[h]\,DF_\tau(x_0)[k]
 + \sum_\sigma\beta_\sigma\,D^2F_\sigma(x_0)[h,k].
\]

`actualPHScalarLoss_hasFDerivAt_fderiv` proves that the derivative map `Dℓ`
has derivative `B` at `x₀`. This establishes existence before identifying the
nested `fderiv`, so the theorem cannot be satisfied by its default value at a
nondifferentiable function. The C² condition implies the existing C¹ condition,
and the first derivative retains the earlier face formula.

The proof differentiates the ordinary composition rule. Its two terms are
`D²φ(z)[DL h,DL k]` and `Dφ(z)[D²L[h,k]]`. Expanding in the face basis twice
and once, respectively, gives the displayed sums. Symmetry of C² second
derivatives gives `Γστ = Γτσ` and `B[h,k] = B[k,h]`. The standard curried
operator norm satisfies

\[
\|D^2\ell(x_0)\| \le
 \sum_\sigma\sum_\tau |\Gamma_{\sigma\tau}|
   \|DF_\sigma(x_0)\|\,\|DF_\tau(x_0)\|
 + \sum_\sigma |\beta_\sigma|\,\|D^2F_\sigma(x_0)\|.
\]

Empty face and coordinate sets are included. If the face second derivatives
vanish at `x₀`, the single sum vanishes. An affine family near `x₀` therefore
has the usual Hessian pullback by its linear part. This is an explicit
specialization; a nonlinear filtration generally needs the curvature sum.

## Presentations and ties

Any two admissible C² local lifts of the same diagram family produce the same
final bilinear form because both differentiate the same scalar function.
Coordinate counts may differ. Neither the coefficient vectors nor the ambient
Hessian arrays are asserted to be unique across presentations.

A persistent diagonal pair retains both coordinates. Equal face-value paths
have equal first and second derivatives at the base point. Cancellation uses
these equalities, without assuming that either ambient coefficient vanishes.
The squared signed endpoint-difference loss has a nonzero ambient Hessian at a
diagonal pair even though its restriction to the diagonal is zero.

## Actual examples

* A singleton with value `t²`, with loss `essentialBirthSum²`, has scalar loss
  `t⁴`. At `t = 1`, the second derivative is `12`: the coordinate-loss term is
  `8` and the face-curvature term is `4`.
* An actual edge has vertex values `0`, `1+s` and edge value `3+t+s²` on
  `|s|, |t| < 1/4`. Its actual degree-zero diagram has essential birth `0` and
  finite interval `(1+s,3+t+s²)`, obtained from the existing actual homology
  fixture by grade transport. For squared signed endpoint difference, the
  loss is `(2+t−s+s²)²`. At the origin the Hessian is
  `[[10,−2],[−2,2]]`; its coordinate contribution is `[[2,−2],[−2,2]]`
  and its face-curvature contribution is `[[8,0],[0,0]]`.
* An actual edge with every face valued `t²` retains a finite template pair.
  The signed loss's nonzero birth and death weights cancel against equal face
  second derivatives. For its square, a nonzero ambient Hessian pulls back
  to zero. Both actual scalar losses have zero second derivative.
* Presentation examples swap unequal essential paths and append a moving
  diagonal pair. The final second derivatives agree. The absolute
  endpoint-difference loss at the empty diagram fails the C² condition,
  because that condition implies the already-disproved C¹ condition there.

The squared losses are coordinate polynomials on every ordered coordinate
space, including representatives augmented by diagonal finite pairs. Their
regularity is not restricted to a positive cone.

## Scope and sources

The local-lift and all-representatives conditions specialize
[Leygonie–Oudot–Tillmann, Definitions 3.3 and 3.10, Proposition 3.14 and
Theorem 4.7](https://doi.org/10.1007/s10208-021-09522-y). The displayed face
Hessian formula is a library consequence of ordinary second-order calculus,
not a formula attributed to that paper. Its analytic ingredients are pinned
mathlib's
[composition of varying continuous linear maps](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean)
and
[symmetry of second derivatives](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean).

All conclusions concern ordinary scalar derivatives. No topology or Hessian on
`Diagram` is installed, and no derivative at an ordering frontier is claimed.
The examples do not depend on the actual simplicial reducer adapter or close
the separate filled-triangle fixture under #45.
