# Unshifted Schanuel interleavings

This module formalizes the module-interleaving step in the proof of
[Botnan–Oppermann–Oudot–Scoccola, Theorem 6.1, §6.1](https://arxiv.org/html/2208.00300v3#S6.SS1).
That proof first applies the persistent Schanuel comparison to obtain an
`ε`-interleaving between alternating sums whose degree-`j` terms are shifted by
`jε`. It then removes the shifts using the resolution length bound and obtains
an interleaving between the unshifted alternating sums at radius
`(2n−1)ε`.

Here the `ε`-interleaving is the existing
`schanuelInterleavingOfResolutions`. The degree bound comes from the original
finite-presentation theorem: for every supplied certified minimal resolution,
the zero-padded term `termAt j` is zero when `j > 2n−2`. This concerns the last
nonzero degree, not a bound on the stored resolution length. The finite sums
remain indexed by the actual maximum of the two stored lengths, so unequal
lengths and arbitrarily long zero padding remain valid inputs.

For `δ=(2n−2)ε`, the source-to-target comparison is asymmetric. On each parity
sum it supplies maps `u : A ⟶ A'` and `v : A' ⟶ shift δ A` with
`u ≫ v = transition δ A` and
`v ≫ (shift δ).map u = transition δ A'`. A degree-`j` summand with
`jε ≤ δ` uses `shiftLE`; a zero summand uses the zero reverse map even when
`jε > δ`. The proof assembles both object-level equations from the actual
biproduct inclusions. The public finite-family API exposes the component maps
and the active-delay/zero cases.

Transporting the shifted Schanuel interleaving through these two comparisons
gives `ε+δ=(2n−1)ε`. The transported maps and both double-transition equations
are proved explicitly. Taking the double infimum over interleaving witnesses
then gives the fixed-resolution extended-distance bound; positive finite
multiplication commutes with both infima, so the proof needs no attainment or
finite-distance assumption.

The public capstone is
`finitelyPresented_unshiftedSchanuel_interleaving`, which accepts any
certified minimal resolutions of modules satisfying the original
`GradedFree.FinitelyPresented` predicates. The companion existence theorem
constructs such resolutions from those hypotheses, and
`finitelyPresented_unshiftedSchanuel_distance_le` is stated for the actual
parity sums of any supplied pair.

This is only the module-interleaving unit of Theorem 6.1. Identifying these
parity sums with the choice-independent signed hook multisets and proving the
signed matching/dissimilarity estimate remain separate work. No optimality or
sharpness statement is made here.
