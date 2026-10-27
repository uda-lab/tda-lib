# Unshifted Schanuel interleavings

Let `k` be any field, let `n ≥ 1`, and let
`M,N : PModule k (Fin n → ℝ)` satisfy the original
`GradedFree.FinitelyPresented` predicates. Let `R` and `S` be any certified
minimal finite rank-projective resolutions of `M` and `N`, and put
`L = max R.resolution.length S.resolution.length`. Using the existing
zero-padded `FiniteRankProjectiveResolution.termAt`, define the actual finite
parity sums

```text
A(R,S) = ⨁ j : Fin L, if Even j.val then R.resolution.termAt j.val
                                  else S.resolution.termAt j.val
B(R,S) = ⨁ j : Fin L, if Even j.val then S.resolution.termAt j.val
                                  else R.resolution.termAt j.val.
```

For each fixed `R,S`, these targets are independent of `ε`. For every finite
`ε : ℝ≥0` and every actual `CoordinateInterleaving ε M N`, the capstone
constructs an actual interleaving

```text
CoordinateInterleaving (((2*n-1 : ℕ) : ℝ≥0) * ε) A(R,S) B(R,S).
```

Writing `d_I` for the extended `coordinateInterleavingDistance`, it also proves
the fixed-resolution inequality

```text
d_I(A(R,S), B(R,S)) ≤ ((2*n-1 : ℕ) : ℝ≥0∞) * d_I(M,N).
```

The distance conclusion assumes neither finite distance nor attainment of an
infimum. The original finite-presentation hypotheses also provide certified
minimal resolutions, giving the separate existence specialization.

The construction follows the module-interleaving step in
[Botnan–Oppermann–Oudot–Scoccola, Theorem 6.1, §6.1](https://arxiv.org/html/2208.00300v3#S6.SS1).
For a given `ε`, define the shifted parity sums

```text
A′(ε) = ⨁ j : Fin L,
  (shift ((j.val : ℝ≥0) * ε)).obj
    (if Even j.val then R.resolution.termAt j.val else S.resolution.termAt j.val)
B′(ε) = ⨁ j : Fin L,
  (shift ((j.val : ℝ≥0) * ε)).obj
    (if Even j.val then S.resolution.termAt j.val else R.resolution.termAt j.val).
```

The existing persistent Schanuel comparison supplies an `ε`-interleaving
between `A′(ε)` and `B′(ε)`. The proved finite-presentation degree bound says
that every supplied minimal resolution has zero-padded terms zero for
`j > 2n−2`. It bounds the last nonzero degree, not the stored resolution
length; the actual sums above remain indexed by the maximum stored length and
allow arbitrarily long zero padding.

Set `δ=(2n−2)ε`. Each pair `(A,A′)` and `(B,B′)` has an asymmetric comparison
with maps `u : X ⟶ X′` and `v : X′ ⟶ shift δ X` satisfying
`u ≫ v = transition δ X` and
`v ≫ (shift δ).map u = transition δ X′`. A degree-`j` summand with
`jε ≤ δ` uses `shiftLE`. A zero summand uses the zero reverse map even if
`jε > δ`. The finite-family API proves the component laws, both assembled
comparison equations, and the inactive-zero case. Transporting the Schanuel
interleaving through both comparisons gives
`ε+δ=(2n−1)ε`, with both transported double-transition equations proved.

The distance proof commutes the positive finite coefficient through both
infima, so empty witness sets and nonattained infima are included. This is only
the module-interleaving unit of Theorem 6.1. The later identification with
choice-independent signed hook multisets and the signed matching/dissimilarity
argument for the `(2n−1)^2` bound remain separate downstream results. No
optimality or sharpness statement is made here.
