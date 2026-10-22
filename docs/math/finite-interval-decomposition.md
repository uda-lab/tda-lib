# Finite interval decomposition

Let `M : PModule k (Fin N)` have finite-dimensional fibers over an arbitrary field `k`.
The field and module carriers share the same arbitrary universe. An interval has natural
endpoints `b < d ≤ N` and support `b ≤ i < d`. Death `N` means survival through the last
observed stage; it does not assert an infinite lifetime or a continuation beyond the data.

The construction inducts on `totalDimension M = ∑ i, dim M(i)`. When this sum is zero,
every fiber is zero, and the unique maps give a natural isomorphism to the empty barcode.
This also covers `N = 0` without selecting an index.

Otherwise choose the earliest nonzero fiber `M(b)` and a nonzero vector `v` in it. Its
images `vᵢ` stay nonzero until a first death `d`, taking `d = N` if no observed image
vanishes. Functoriality makes every later image zero. At `t = d - 1`, choose a linear
functional `λ` with `λ(vₜ) = 1`. The interval inclusion sends `a` to `a vᵢ` on active
fibers. Its retraction at an active index `i` is `λ ∘ M(i ≤ t)`; elsewhere it is zero.
The retraction is natural across the birth boundary because every fiber before `b` is
zero. Both maps commute with every structure map, and their composite on the interval
is the identity.

The complementary module consists of the kernels of these retraction components. The
splitting maps are

```text
x ↦ (πᵢ(x), x - ιᵢ(πᵢ(x)))
(a, y) ↦ ιᵢ(a) + y.
```

Their inverse identities and naturality give a genuine natural isomorphism. Product
dimension shows that removing the nonempty interval strictly reduces total dimension.
Induction decomposes the complement, and adjoining the extracted occurrence constructs
`exists_barcode_decomposition`.

Only then does `rankBarcode_eq_of_iso_barcodeModule` identify the constructed multiset
with `rankBarcode M`. The chosen `rankBarcodeIso M` is generally noncanonical: the
generators, functionals and complements involve choices. The barcode itself is canonical.
Composing these constructed isomorphisms proves that natural-isomorphism existence,
canonical-barcode equality, and equality of every structure-map rank are equivalent.
The existing four-rank multiplicity laws also show that any two decomposition multisets
are equal. No uniqueness of the chosen summands or isomorphisms is asserted.

The explicit examples include an arbitrary nonzero scalar transition, repeated occurrences, delayed
birth and final-stage survival. The diagrams `k → k² → k` with first map `x ↦ (x,0)` and
second map respectively `(a,b) ↦ b` or `(a,b) ↦ a` have equal stage dimensions and equal
adjacent ranks, but composite ranks zero and one. Their barcodes are respectively
`[0,2) + [1,3)` and `[0,3) + [1,2)`. Thus even diagonal and adjacent ranks together do not
classify a module.

[Chazal–Crawley-Boevey–de Silva, §1.1](https://arxiv.org/pdf/1405.5644v1) states finite
interval decomposition, uniqueness of multiplicities and their four-rank formula. Its
closed discrete interval `[p,q]` becomes `[p,q+1)` here. The elementary earliest-birth
splitting is the finite proof used in this library; it does not formalize the paper's
observable categories or real-index results.
