# Matching distance along positive affine slices

Let $M,N$ be persistence modules on $\mathbb R^n$, with $n\ge1$, and let
$L(t)=b+ta$ have every $a_i>0$. Put $w(L)=\min_i a_i$. The positive minimum
slope controls how a diagonal coordinate shift fits along the line:

$$L(t)+\varepsilon\mathbf1\le L(t+\varepsilon/w(L)).$$

Consequently, an actual coordinate $\varepsilon$-interleaving induces an
actual real $\varepsilon/w(L)$-interleaving of the two restrictions. This
construction works over arbitrary coefficient rings and uses the original
module structure maps.

## The restricted interleaving maps

Let $\alpha_x:M(x)\to N(x+\varepsilon\mathbf1)$ be a supplied forward
interleaving map and put $\delta=\varepsilon/w(L)$. The restricted component
is the composite

$$M(L(t))\xrightarrow{\alpha_{L(t)}}N(L(t)+\varepsilon\mathbf1)
  \longrightarrow N(L(t+\delta)).$$

The second arrow is the actual structure map for the displayed coordinate
inequality. The reverse component is defined in the same way. Naturality
and the original double-shift equations prove both restricted interleaving
equations. With unequal slopes, the second arrow can be nontrivial.

`AffineSliceInterleaving` constructs these maps and exposes their component
equations. It passes from witnesses to the extended infimum defining
interleaving distance, obtaining

$$w(L)\,d_I(M\circ L,N\circ L)\le d_I(M,N).$$

The proof includes zero interleaving radius and infinite extended distances;
it assumes no minimizing interleaving.

## Ordinary barcodes and the normalized supremum

Now take coefficients in an arbitrary field and suppose that $M,N$ have
original finite graded-free presentations. The [slice presentation theorem](positive-affine-slices.md)
derives the same property for their actual restrictions. Let $B_L(M)$ and
$B_L(N)$ be their existing ordinary finite barcodes. The one-dimensional
barcode isometry gives

$$w(L)\,d_B(B_L(M),B_L(N))\le d_I(M,N).$$

`PositiveAffineLine.ordinarySliceBarcode` constructs the barcode from the
original presentation and exposes its positivity and actual realization.
`weightedSliceBottleneck` is the weighted ordinary bottleneck value above.

Normalize the lines by

$$\max_i a_i=1,\qquad\sum_i b_i=0.$$

This family is nonempty: the diagonal line with slopes one and offsets zero
is normalized. Define matching distance by

$$d_{\mathrm{match}}(M,N)=
  \sup_{L\ \mathrm{normalized}}w(L)\,d_B(B_L(M),B_L(N)).$$

`sliceMatchingDistance_le_coordinateInterleavingDistance` proves that this
extended supremum is at most coordinate interleaving distance. Self-distance
is zero, symmetry and the extended triangle inequality hold, and natural
isomorphisms preserve the value. These are extended pseudometric laws;
no separation or completeness theorem for module isomorphism classes is
asserted. The definition uses actual ordinary slice barcodes.

The witness construction corresponds to [Landi, Lemma 1](https://arxiv.org/pdf/1412.3374v1),
and the normalized bound to Theorem 1 of the same version. The source states
the barcode result for pointwise finite-dimensional modules; this library
consumer uses original finite presentations, from which the finite slice
barcodes are derived. The per-line estimate permits arbitrary positive
slopes. Equivalence with a supremum over an unnormalized family and finite
attainment of the supremum are outside these statements.
