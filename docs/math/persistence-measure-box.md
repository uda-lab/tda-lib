# Interleavings and rectangle measures

Let M and N be real persistence modules over the same field and let ε ≥ 0.
Suppose a ≤ b, c ≤ d, b+ε ≤ c−ε, and the image of
N(b+ε) → N(c−ε) is finite-dimensional. An ε-interleaving bounds the
measure of a rectangle for M by the measure of its ε-thickening for N:

\[
\mu_M([a,b]\times[c,d])\le
\mu_N([a-\varepsilon,b+\varepsilon]\times[c-\varepsilon,d+\varepsilon]).
\]

The measure uses the image-and-kernel quotient described
in [persistence rectangle measures](persistence-rectangle-measure.md), so an
interval contributes when it contains b and c and excludes a and d. The proof
retains this boundary convention.

`RealInterleaving.persistenceMeasureValue_box_le` requires b+ε ≤ c−ε and
finite-dimensionality of the image of N(b+ε) → N(c−ε). It needs no
finite-dimensional fiber assumption. The corollary
`RealInterleaving.persistenceMeasureValue_box_le_of_qTame` obtains this local
finiteness from q-tameness of N and the strict separation 2ε < c−b.
Neither statement requires q-tameness of M or a vanishing lower tail.
Applying the theorem to the reversed interleaving gives the opposite box
inequality under the corresponding local finiteness assumption for M.

The proof uses the interleaving equations to factor M(b) → M(c) through
N(b+ε) → N(c−ε). Classes killed by d lift to classes killed by d+ε;
classes from N(a−ε) map into the image from M(a). A quotient of a subspace
of the expanded rectangle's numerator therefore surjects onto the original
rectangle quotient. Its dimension is bounded by that of the expanded quotient.
The public `RealInterleaving.crossing_factorization` exposes the factorization.

The displaced intervals [0,2) and [1/4,9/4) give a positive-parameter fixture:
the first rectangle [-1,0] × [1,2] has measure one, and the theorem proves
positive measure on [-5/4,1/4] × [3/4,9/4] for the second interval. Both
shifted endpoints lie on upper rectangle edges.

The source is Chazal–de Silva–Glisse–Oudot,
[*The structure and stability of persistence modules*, arXiv:1207.3674v3](https://arxiv.org/pdf/1207.3674v3),
Lemma 4.22 in §4.6. This result concerns finite rectangles. Diagram construction,
essential-boundary comparison and the matching argument of Theorems 4.20–4.21
remain separate results; the finite-rectangle box inequality alone does not
establish bottleneck stability.
