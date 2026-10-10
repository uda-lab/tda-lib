# Finite support-aware face presentations

## Construction

For `n : ℕ`, `TDA.Simplicial.FiniteComplex n` stores a `Finset` of finite subsets of `Fin n`,
with proofs that listed faces are nonempty and every nonempty subface of a listed face is also
listed. `toPre` converts the stored collection to a
`PreAbstractSimplicialComplex (Fin n)` whose face predicate is exactly membership in that
collection. Thus ambient vertices may remain unsupported, and the empty face is excluded.

The conversion has a direct `DecidablePred` from stored `Finset` membership and a
`Fintype (TDA.Simplicial.TotalFace C.toPre)` built by `Fintype.subtype C.faces`. The finite
enumeration carries proofs on the stored faces themselves. It does not enumerate a powerset,
complete missing faces, or choose faces from a proof of finiteness.

## Public laws

`mem_toPre` identifies converted membership with stored membership, and
`empty_not_mem_faces` records the nonempty-face invariant. `image_univ_totalFace_val` says that
forgetting membership proofs from every enumerated face gives exactly the stored collection.
`card_totalFace` identifies the number of actual faces with `C.faces.card`.
`toPre_injective` says that this conversion retains the full presentation data up to proof
irrelevance. These results concern finite sets and the existing complex structure; they assert
no persistence, homology, or external TDA theorem.

## Source correspondence

- `TDA/Simplicial/Bridge.lean` at base commit
  `1a7073442a05708f12eeb07164c2b35ec9893c1c` (blob
  `a811965673ef1d3da54efe0aef768bcbf3ae1d50`) defines
  `TDA.Simplicial.TotalFace K` as the existing subtype `{s : Finset V // s ∈ K}`.
- Mathlib's `PreAbstractSimplicialComplex` and relative-lower-set field are from pinned mathlib
  revision `0df444a360eaa60ab8c11dca51a86af692955474`,
  `Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean` (blob
  `7c9a30a86c7b60749a466923379cfe1eabd50c87`).
- Mathlib's direct subtype enumeration is `Fintype.subtype` in
  `Mathlib/Data/Fintype/Defs.lean` at that same pinned revision (blob
  `c9fab2c73ea097b3d5765e9b81817977bdd75f82`). `Fintype.ofInjective`, whose implementation is
  noncomputable, is not used.
- The integration fixture in `TDA/Simplicial/FiniteComplexExamples.lean` uses the existing
  `TDA.Filtration.FilterFunction` API from `TDA/Filtration/FilterFunction.lean` at the same
  base commit (blob `bcf4907aaec0a1cb2ce116c661230a115fdf4a65`). The constant face value checks
  bottom and full sublevels while preserving the absent ambient vertex. No external persistence
  statement is translated.

The Issue #97 interface and acceptance conditions specify the finite presentation's exact
scope. No compatible ordering of faces, orientation, boundary, homology, barcode convention,
parser, or arbitrary-complex reverse conversion is supplied here.
