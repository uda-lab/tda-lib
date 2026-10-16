# Canonical barcode embeddings from finite-chain epimorphisms

## Modules, endpoints and occurrence order

Fix a field `k : Type u` and pointwise finite-dimensional modules
`M N : PModule.{u,0,u} k (Fin s)`. The input is an actual natural transformation
`p : M ⟶ N` and surjectivity of every `(p.app i).hom`.

Write `B = rankBarcode M` and `C = rankBarcode N`. An interval has natural endpoints
`birth < death ≤ s` and uses the half-open convention `[birth,death)`. Death `s`
means survival through the last observed stage. `BarcodeOccurrence s B` retains
the indices of `B.toList`, so repeated interval values have distinct labels.

At a fixed birth `b`, `FiniteBarcode.BirthOccurrence B b` retains an occurrence
index and its birth equality. Its order is descending death, then ascending
original index. `birthEnumeration` enumerates this finite ordered set, and
`birthOrdinal` gives an occurrence's zero-based position in its birth group.
Thus longer intervals come first, including terminal bars. This order specifies
the canonical correspondence relative to the existing labels.

## Survival counts from actual image quotients

Let `birthSuffixCount B b c` count occurrences with birth exactly `b` and death
strictly greater than `c`. For `0 < b ≤ c < s`, put

```text
W_M(b,c) = image M(b → c),
U_M(b,c) = image M(b−1 → c),
Q_M(b,c) = W_M(b,c) / U_M(b,c).
```

Structure-map composition puts `U_M(b,c)` inside `W_M(b,c)`.
`birthPreviousImage` represents this preceding image as a submodule of `W_M`.
The bounds justify all finite indices and the predecessor.

The barcode rank formula partitions `rank M(b → c)` into the intervals born
at `b` that survive at `c` and those born earlier. Quotient rank-nullity gives
the same additive partition with `dim Q_M(b,c)` in the first term. Comparing
these equalities proves `birthSuffixCount_eq_finrank`:

```text
birthSuffixCount (rankBarcode M) b c = dim Q_M(b,c),  0 < b ≤ c < s.
```

Naturality restricts `p(c)` to a map `W_M → W_N` and sends `U_M` into `U_N`,
so it induces an actual map `Q_M → Q_N`. To see that the restricted image map
is surjective, write an element of `W_N` as `N(b → c)(y)`, lift `y` along the
surjection `p(b)`, and use naturality. The induced quotient map is therefore
surjective as well. Comparing its dimensions proves the count inequality;
subtracting unrelated rank inequalities would not give this conclusion.

Birth zero has no preceding stage. `birthSuffixCount_zero` identifies its
survival count with `rank M(0 → c)`. The same image-map argument proves the
comparison directly. Together these cases give
`birthSuffixCount_le_of_surjective` for `b ≤ c < s`.

Terminal bars are included at `c = s−1`, whenever a bar exists. Such an
occurrence supplies `s > 0` before this index is formed. With `s = 0` there
are no intervals or occurrence labels, and no stage is selected.

## The canonical embedding and its laws

Taking `c = b` bounds each target birth group's size by the source group's size.
`FiniteBarcode.epiEmbedding p hp` sends target ordinal `r` to source ordinal
`r` at the same birth. It is an actual embedding `O(C) ↪ O(B)`.

For a target interval `I`, use the cutoff `I.death−1`. Its birth-group prefix
through ordinal `r` contains at least `r+1` intervals surviving this cutoff.
If its corresponding source interval died earlier, at most `r` source
intervals could survive the cutoff, contradicting the count inequality.
Thus the corresponding source bar has death at least `I.death`.
`epiEmbedding_terminal` combines this bound with `death ≤ s` to preserve
terminal survival exactly.

Birth and ordinal uniquely characterize the embedding in `epiEmbedding_eq_iff`.
They give `epiEmbedding_id` and the contravariant composition law
`epiEmbedding_comp`: for epis `p : M ⟶ N` and `q : N ⟶ P`, the embedding for
`p ≫ q` is the embedding `O(P) ↪ O(N)` followed by `O(N) ↪ O(M)`.
These laws concern epimorphisms only.

Consumers use actual interval truncations `[0,3) → [0,2) → [0,1)`, a positive-birth
quotient, a one-stage projection from three to two repeated bars, and an empty
chain. The rank-only boundary uses `[1,2)` and `[0,3)` on `Fin 3`: all structure-map
ranks of the first are bounded by those of the second, but their different births
exclude a birth-preserving occurrence embedding.

## Source correspondence and scope

Manifestation, attribution and rights: [BL15-v4](references.md#BL15-v4).
The statement and canonical birth-group order are the finite-chain specialization
of [Bauer–Lesnick v4, §4.1 and Theorem 4.2(ii)](https://arxiv.org/html/1311.3681v4#S4).
The epi composition law specializes
[Proposition 5.7](https://arxiv.org/html/1311.3681v4#S5.SS2).
The paper proves the epi statement by duality from its mono statement, using
Proposition 3.7. Here the direct image-quotient surjections provide the proof.
The predecessor and initial-stage cases and the list-index tie break are explicit
library implementation choices; no order-reversal or linear-dual adapter is claimed.

The [mono embedding](finite-mono-matching.md) and this epi embedding provide the
two canonical correspondences separately. A general epi need not match every
source occurrence, including terminal ones. The distance-specific
`OccurrenceMatching`, with its total essential equivalence, is therefore a
different interface. General-morphism composition, quantitative induced matching,
real-grid refinement and shifts, constructible kernel/image/cokernel closure and
the reverse inequality `d_B ≤ d_I` remain separate results.
