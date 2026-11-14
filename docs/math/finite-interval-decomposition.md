# Finite interval decomposition

Let `M : PModule k (Fin N)` have finite-dimensional fibers over an arbitrary field `k`.
The field and module carriers share the same arbitrary universe. An interval has natural
endpoints `b < d ≤ N` and support `b ≤ i < d`. Death `N` means survival through the last
observed stage; it does not assert an infinite lifetime or a continuation beyond the data.

## Using the existence result

Import [`TDA.Persistence.FiniteDecomposition`](../../TDA/Persistence/FiniteDecomposition.lean) to use the existence theorem:

```lean
import TDA.Persistence.FiniteDecomposition

open CategoryTheory TDA.Persistence

universe u
variable (k : Type u) [Field k]
variable (N : ℕ)
variable (M : PModule.{u,0,u} k (Fin N))
variable [∀ i : Fin N, FiniteDimensional k (M.obj i)]

example : Nonempty (M ≅ barcodeModule (k := k) (rankBarcode M)) :=
  nonempty_rankBarcodeIso M
```

`Nonempty` states that such a natural isomorphism exists; this example needs no supplied basis
or interval decomposition. `rankBarcode M` is canonical, while `rankBarcodeIso M` is a chosen,
generally noncanonical natural isomorphism defined noncomputably. No positive-length assumption
on `N` is needed, so `N = 0` is included. For the separate fixed-F₂, integer-grade simplex-list
computation, see the [first-run example](finite-ph-computation.md#first-run).

## Construction

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
birth and final-stage survival.

## Three-stage comparison

Over any field `k`, both `Fin 3` examples have fibers `k`, `k × k`, and `k` at stages
`0`, `1`, and `2`. Both have stage dimensions `(1, 2, 1)` and adjacent-map ranks `(1, 1)`.
Their common first map is `x ↦ (x, 0)`. The composite rank still depends on which
coordinate the second map keeps:

| Module | Second map (`k × k → k`) | Composite rank (`0 → 2`) | Barcode |
|---|---|---:|---|
| `compositeZero` | `(a, b) ↦ b` | `0` | `[0,2) + [1,3)` |
| `compositeIdentity` | `(a, b) ↦ a` | `1` | `[0,3) + [1,2)` |

With the second projection, the first coordinate carried from stage `0` is discarded at
stage `2`, while the second coordinate born at stage `1` survives. With the first projection,
the first coordinate survives through stage `2` and the second coordinate is discarded.
Endpoint `3` records survival through the last observed stage `2`; it does not mean an
infinite lifetime. Thus the same dimensions and adjacent ranks do not determine the
composite rank, barcode, or isomorphism class.

The [standalone three-stage fixture](../../TDA/Persistence/FiniteDecompositionThreeStage.lean)
defines `compositeZero` and `compositeIdentity` in namespace
`TDA.Persistence.ThreeStageExamples`; import `TDA.Persistence.FiniteDecompositionThreeStage`
to use them. Its public `dimensions_and_adjacent_ranks_agree`, `composite_ranks`,
`zero_rankBarcode`, and `identity_rankBarcode` declarations establish the comparison.

## Source scope

[Chazal–Crawley-Boevey–de Silva, §1.1](https://arxiv.org/pdf/1405.5644v1) states finite
interval decomposition, uniqueness of multiplicities and their four-rank formula. Its
closed discrete interval `[p,q]` becomes `[p,q+1)` here. The elementary earliest-birth
splitting is the finite proof used in this library; it does not formalize the paper's
observable categories or real-index results.
