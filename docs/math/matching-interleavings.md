# From a finite barcode matching to an interleaving

A matching with cost at most ε compares two finite barcodes by pairing nearby
intervals and leaving sufficiently short intervals unpaired. Over a field, the
construction below turns that matching into two actual natural transformations
between the barcode realizations. Their composites are the original structure
maps across twice the shift.

## Inputs and endpoint conventions

Fix a field `k`, positive finite diagrams `D E : Diagram ℝ`, and `ε : ℝ≥0`.
A finite point `(b,d)` represents `[b,d)`; an essential point `(b,⊤)` represents
`[b,∞)`. Birth is included and finite death is excluded. Positivity is explicit:
the underlying `Diagram` type also permits reversed off-diagonal pairs.
Occurrences label coordinates, so repeated endpoint pairs remain separate.

The existing `OccurrenceMatching` supplies a partial injection between finite
occurrences and a total equivalence between essential occurrences. Its cost is
the maximum of the matched and unmatched contributions:

- A matched finite pair contributes `max (|b−c|) (|d−e|)`.
- An unmatched finite interval contributes half its length on either side.
- A matched essential pair contributes the absolute difference of its births.

Thus cost ≤ ε bounds both endpoints of each finite pair by ε, every unmatched
finite length by `2ε`, and each paired essential birth difference by ε. Essential
occurrences are neither deleted nor paired with finite intervals.

`RealBarcode.matchingInterleaving` accepts this matching and numeric cost bound
and returns `RealInterleaving ε (realize D) (realize E)`. It constructs the
interval comparisons and coordinate isomorphisms from the endpoint data.

## The interval maps

Write `I=[b,d)` and `J=[c,e)`, with infinite deaths allowed. The shift convention
is `(SεJ)t=J(t+ε)`, so a positive shift moves support left. The normalized comparison
`I → SεJ` preserves the coefficient where both fibers are alive and is zero
elsewhere. The bounds `c ≤ b+ε` and `e ≤ d+ε` make it natural; infinity plus a
finite parameter is infinity. Under these bounds, a positive source has a nonzero
comparison exactly when `b+ε < e`. Equality gives contact with the excluded death
and hence the zero map. No full classification of arbitrary interval morphisms
is required by this construction.

The endpoint bounds from a finite matched pair give comparisons in both
directions. Essential pairs use the same construction with infinite deaths.
`interleavingOfBounds` proves both composite equations, including the canonical
shift-composition identification. If the source is alive at `t` and `t+2ε`, the
bounds force the other interval to be alive at `t+ε`; all three coefficient maps
then preserve the coefficient. Otherwise the original structure map and the
composite both vanish. Either comparison may itself be zero.

Write `η²ε` for the transition from `t` to `t+2ε`. For a finite interval,
`transition_eq_zero_iff` and `interleaved_zero_iff` give

\[
\eta^{2\varepsilon}_{[b,d)}=0
\quad\Longleftrightarrow\quad
[b,d)\text{ is }\varepsilon\text{-interleaved with }0
\quad\Longleftrightarrow\quad d-b\le 2\varepsilon.
\]

The length equality is included because `d` is excluded. A longer positive
interval has a nonzero structure map from its birth to birth plus `2ε`.
`essential_not_interleaved_zero` gives the corresponding failure for every
essential birth and every finite ε. The negative claims use the field's `1≠0`.

## Assembling the realization maps

`occurrenceModule` presents the barcode with finite and essential occurrence
coordinates. `occurrenceIso` identifies it naturally with the existing `realize`
list, preserving every occurrence and every structure map. The finite partial
injection and its inverse select paired coordinates; unmatched coordinates receive
zero maps. The essential equivalence selects every essential coordinate.

The two composite equations are checked coordinate by coordinate. Matched
coordinates use `interleavingOfBounds`; unmatched coordinates use the proved
length criterion. The constructed occurrence isomorphisms then transport these
maps to the actual realizations. The finite coordinate product is the existing
barcode product; `familyModule` and `familyIso` expose that construction and its
coordinate change. No dimension or rank equality substitutes for a natural map.

Examples include exact endpoint displacement, one zero comparison in a matched
pair, deletion at length `2ε`, essential birth displacement, two identical bars
against one, empty diagrams at every finite parameter, and ε=0.

## Source correspondence and scope

[Bauer–Lesnick, arXiv:1311.3681v4](https://arxiv.org/html/1311.3681v4#S8.SS1),
§§3.1–3.2 and §8.1, supplies the matching-to-interleaving construction of
Theorem 8.2. The library result is its finite, left-closed/right-open specialization;
occurrence coordinates and the explicit natural-isomorphism transport are library
glue. Source identity and rights are recorded in [BL15-v4](references.md#BL15-v4).

Lemma 8.1 leaves its proof details to the reader. Its item (ii), in both v4 HTML
and PDF page 26, writes `b+ε ≥ d` after fixing δ, without relating those symbols
there. The precise half-open criterion used here is proved from the double-shift
equations and the actual structure maps: `d−b ≤ 2ε`. These numeric equality rules apply to the fixed half-open convention; other
endpoint decorations require their own boundary conditions.

Interleaving distance, infimum and attainment laws, the reverse construction from
interleavings to matchings, and either distance isometry inequality are separate
results. This construction uses no generic flow, infinite barcode or q-tame theory.
