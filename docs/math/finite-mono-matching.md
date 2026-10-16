# Canonical barcode embeddings from finite-chain monomorphisms

A componentwise injective natural transformation between finite persistence modules
gives an injection of their barcode occurrences. Each target bar has the same observed
death as its source and is born no later. The injection pairs equal positions in a fixed
order, so identities and compositions of monomorphisms induce identities and compositions
of occurrence embeddings.

## Modules, endpoints and occurrence order

Fix `k : Type u` with `[Field k]`, a chain `Fin s`, and
`M N : PModule.{u,0,u} k (Fin s)` with finite-dimensional fibers at every stage.
The input is an actual natural transformation `j : M ⟶ N` and injectivity of each
`(j.app i).hom`. Neither a barcode matching nor a decomposition is supplied.

Write `B = rankBarcode M` and `C = rankBarcode N`. Their intervals satisfy
`birth < death ≤ s` and use the half-open convention. Death `s` means survival
through the last observed stage; it acquires an essential real tail only when used
in the separate constructible real-module reconstruction.

`BarcodeOccurrence s B` retains the indices of `B.toList`. Equal interval values
therefore have distinct labels. At a fixed death `d`, `FiniteBarcode.DeathOccurrence`
retains the original index and its death equality. Order this group by ascending birth,
breaking ties by the original occurrence index. `deathEnumeration` is its increasing
finite enumeration, and `deathOrdinal` is an occurrence's zero-based position.
These definitions make the correspondence canonical relative to the existing labels;
they do not select interval generators or bases.

## From actual subspaces to cumulative counts

Let `deathPrefixCount B b d` count the occurrences with birth at most `b` and death
exactly `d`. For `b < d < s`, set

```text
U_M(b,d) = image M(b → d−1) ∩ kernel M(d−1 → d).
```

`deathSubspace` is this actual submodule of `M(d−1)`. The inequalities supply the
finite indices and justify the predecessor. The barcode rank formula partitions
`rank M(b → d−1)` into bars dying at `d` and bars surviving beyond `d`.
The restricted rank-nullity formula identifies the same rank drop with the dimension
of `U_M(b,d)`. Hence `deathPrefixCount_eq_finrank` proves

```text
deathPrefixCount (rankBarcode M) b d = dim U_M(b,d),  b < d < s.
```

Naturality sends `U_M(b,d)` into `U_N(b,d)`: it sends images into images and
kernels into kernels. Restricting `j(d−1)` gives an actual linear injection between
these subspaces, whose dimensions can then be compared. Subtracting unrelated rank
inequalities would not justify this step.

For `b < d = s`, `deathPrefixCount_terminal` instead counts the image of
`M(b → s−1)`. The inequality `b < s` supplies a positive chain size. Restricting
`j(s−1)` gives the corresponding injection of terminal images. With `s = 0`, there
are no interval occurrences and neither formula selects a predecessor.

Together these cases prove `deathPrefixCount_le_of_injective` for `b < d ≤ s`.

## The standard occurrence embedding

Taking the cutoff `d−1` bounds the size of each nonempty source death group by the
target group's size. `FiniteBarcode.monoEmbedding j hj` maps the occurrence of ordinal
`r` to target ordinal `r` at that same death. It is an actual embedding of all source
occurrence labels into all target labels.

The cumulative inequality also proves the birth bound. The source prefix through
the source bar's birth contains at least `r+1` occurrences. If the target at ordinal
`r` were born later, its prefix through that birth cutoff would contain at most `r`
occurrences, contradicting the inequality. The API exposes death preservation, the
birth bound and the death/ordinal characterization in `monoEmbedding_eq_iff`.

The characterization gives `monoEmbedding_id` and `monoEmbedding_comp`: composing
monomorphisms preserves the same death and ordinal. No composition law for arbitrary
persistence-module morphisms is asserted.

## Examples and scope

Consumers use actual inclusions `[2,3) → [1,3) → [0,3)`, duplicate one-stage bars,
an empty chain, and a bar dying before the final observed stage. Distinct duplicate
labels remain distinct. The rank-domination boundary uses `[1,2)` and `[0,3)` on
`Fin 3`: all source structure-map ranks are bounded by the target ranks, but their
different deaths exclude a death-preserving occurrence embedding.

This mono embedding need not cover every target terminal bar. The distance-specific
`OccurrenceMatching` requires a total equivalence of essential occurrences and is
therefore not the input or output type here. Epi matching, quantitative induced
matching, common real-grid refinement, shift compatibility and constructible
kernel/image/cokernel closure are separate connections needed for the reverse
interleaving-distance inequality.

## Source correspondence

Manifestation, attribution and rights: [BL15-v4](references.md#BL15-v4).
The finite-chain mono statement follows the structure theorem in
[Bauer–Lesnick v4, Theorem 4.2(i) and Lemma 4.3](https://arxiv.org/html/1311.3681v4#S4),
with the monomorphism composition rule in
[Proposition 5.7](https://arxiv.org/html/1311.3681v4#S5.SS2).
Their same-death ordering puts longer intervals first, which is ascending birth here.
The actual image/kernel injection implements the proof-critical comparison; finite
predecessors, the terminal-image case and the list-index tie break are explicit library
representation details. This result does not establish the quantitative induced
matching theorem or `d_B ≤ d_I`.
