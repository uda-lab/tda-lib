# Kernel and cokernel shortness from a real interleaving

An actual ε-interleaving forces the kernel and cokernel of either comparison
morphism to have zero transition across `2ε`. This supplies an algebraic input
to induced matching estimates without assuming a matching or a barcode decomposition.

## Objects and parameters

Fix a ring `R : Type u` and real-indexed modules
`M N : PModule.{u,0,w} R ℝ`. The carrier universe `w` is independent of `u`.
The shift parameter `ε : ℝ≥0` is finite, and the
[real shift](real-interleavings.md#modules-parameters-and-shifts) has positive
evaluation direction: `(SεN)(t)=N(t+ε)`.

Let `i : RealInterleaving ε M N`, with actual natural transformations
`f=i.φ : M → SεN` and `g=i.ψ : N → SεM`. Their component equations, before
the canonical addition transport, are

\[
g_{t+\varepsilon}f_t=M[t\le(t+\varepsilon)+\varepsilon],\qquad
f_{t+\varepsilon}g_t=N[t\le(t+\varepsilon)+\varepsilon].
\]

Write `K=kernel f` and `C=cokernel f` for mathlib's actual objects in the
functor category. Their inclusion `κ:K→M` and projection `π:SεN→C` are
natural transformations. Write `η_A^δ` for the actual transition
`RealShift.transition δ A`. A module is δ-trivial when this morphism is zero.

## The two annihilation statements

In `TDA.Persistence.RealInterleavingShortness`, the theorems
`RealInterleaving.kernel_transition_eq_zero` and
`RealInterleaving.cokernel_transition_eq_zero` prove

\[
\eta_K^{2\varepsilon}=0,\qquad \eta_C^{2\varepsilon}=0.
\]

No finite-dimensionality, constructibility or chosen decomposition is needed.
The same statements for `g` follow by applying them to `i.symm`.

For the kernel, naturality of κ expresses its transition followed by the later
inclusion as `κ_t` followed by the transition of M. The first interleaving
equation factors that transition through `f_t`. Since `f_t κ_t=0`, cancellation
of the later monomorphism gives the zero kernel transition.

For the cokernel, precompose its transition with the earlier epimorphism `π_t`.
Naturality identifies the result with the transition of `SεN`, followed by the
later projection. Apply the second interleaving equation **at `t+ε`**:
the transition of N from `t+ε` to `((t+ε)+ε)+ε` factors through
`f_((t+ε)+ε)`. The cokernel relation kills this final factor. Cancellation of
`π_t` gives the zero cokernel transition.

Both arguments first reach the nested index `(t+ε)+ε`. Applying the actual
functor map along `(t+ε)+ε=t+(ε+ε)` transports these zero maps to the declared
double-shift transition. This keeps the shifted target in the cokernel argument
and the addition identification explicit.

## Sharp threshold and parameter zero

The actual rational interval module `[0,2)` has zero two-transition. Thus zero
forward and reverse maps define a one-interleaving of this nonzero module with
itself. Its actual kernel is isomorphic to `[0,2)`, and its actual cokernel to
the shifted interval `[-1,1)`, by the categorical zero-morphism isomorphisms.
The one-transitions of both defects are nonzero: evaluate at `0` for the kernel
and at `-1` for the cokernel. Both retain coefficient one. Consequently the
factor two cannot uniformly be replaced by one, including at the half-open
length-equals-two boundary.

At parameter zero an actual natural isomorphism of the constant integer module
gives a zero-interleaving. The proved shortness and the canonical zero-shift
unit imply that both actual defects are zero objects, while the original
constant module has nonzero fibers.

These consumers are in `TDA.Persistence.RealInterleavingShortnessExamples`.

## Source correspondence and remaining bridge

[Bauer–Lesnick v4](https://arxiv.org/html/1311.3681v4#S6.SS1), Lemma 6.3,
states the `2ε`-triviality of the kernel and cokernel of an interleaving morphism;
its short proof refers directly to the interleaving definition in §3.1.
The source's ε-triviality in §6 is exactly vanishing of the transition morphism.
The field-valued statement is a specialization of these Lean results, which
also cover ring-valued modules and impose no dimension hypothesis. The proof
above establishes this extension using categorical kernels and cokernels.
Source and rights metadata are recorded in [BL15-v4](references.md#BL15-v4).

Lemma 6.2 is the separate duality statement, whose proof the source omits;
this argument does not use it. The
[constructible defect and sampling bridge](constructible-defects-sampling.md)
derives actual defect constructibility on a common grid and transfers this
annihilation to the actual finite sampled kernels and cokernels. The
[finite quantitative induced matching](finite-quantitative-induced-matching.md)
retains its finite-dimensionality and endpoint hypotheses. Real barcode shift
correspondence, real matching existence and `d_B≤d_I` remain separate results.
