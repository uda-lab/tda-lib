# Ordinary projective dimensions of actual incidence modules

Let `k` be any field and `S` a finite bounded lattice. Let `R` be the actual
right-incidence ring on the interval-pair poset `PairPoset S`, and let `C` be
the actual right-module ring of its diagonal quotient. Write
`D(PairPoset S) = maxComplementCard (S := PairPoset S)`.

For every finite-dimensional actual right `R`-module `M`,
`TDA.Persistence.IncidenceVertexProjectiveDimension.hasProjectiveDimensionLE`
proves
`HasProjectiveDimensionLE M (D(PairPoset S))`. The same bound holds for every
finite-dimensional actual right `C`-module, measured using its canonical
restricted `k`-action, by `quotient_hasProjectiveDimensionLE`. No projective
resolution or projective-dimension bound is supplied as input.

The comparison theorem
`hasProjectiveDimensionLE_of_vertex` first transfers any bound on the ordinary
projective dimension of the actual all-vertex representation of a finite-
dimensional `R`-module back to the module. It uses finite-free covers, field
finite-dimensionality of their kernels, exactness of the actual vertex
functor, and projectivity of the regular module's vertex image. The latter is
identified with the graded-free module on interval-pair vertices by
`IncidenceRegularVertex.regularVertexIso`. The existing representation bound
then supplies `D(PairPoset S)` without an extra dimension hypothesis.

For an actual coordinate grid `G : CoordinateGrid n` with nonempty factors and
`n ≥ 1`, the actual incidence and quotient module theorems give bounds `2*n`
for every finite-dimensional module over their respective rings. The
coefficient field remains arbitrary; finite-dimensionality is over the actual
restricted `k`-action, not a finite-field or finite-carrier assumption.

The representation result is for actual `PModule` objects, and this module
comparison is for finite-dimensional incidence modules. Together they do not
assert essential surjectivity of the vertex representation, an equivalence
with all persistence modules, or finite projective dimension for arbitrary
incidence modules. They do not bound the Hom-cokernel used in minimal relative
rank-resolution comparisons, prove the relative `2n−2` estimate, or establish
a stability result.

The source context is BOOS24-v3 §2.4, Lemma 2.1 and Remark 2.2, together with
the ordinary-dimension ingredient around Theorem 5.16. The library gives an
explicit finite-free dimension-reflection proof through its actual vertex
representation and representation-category dimension result; it does not
claim the whole source equivalence or a correction to the paper. See
[BOOS24-v3 in the reference register](references.md#BOOS24-v3).
