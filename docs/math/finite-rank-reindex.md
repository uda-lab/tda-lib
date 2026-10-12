# Finite monotone sampling of ranks and barcodes

Let `M : PModule.{u,0,u} k (Fin L)` have finite-dimensional fibers over a field `k`, and let `s : Fin N →o Fin L` be monotone. `reindex s M` observes the source module at the sample stages, with the actual source structure maps between them. Sample indices may repeat or skip stages; neither size is required to be positive. The finite rank API's existing universe parameters are retained.

## Endpoint cuts and interval restriction

For every natural endpoint `e`, `sampledEndpoint s e` is the number of occurrences `j : Fin N` with `(s j).val < e`. Monotonicity makes this set an initial segment, so

`j.val < sampledEndpoint s e ↔ (s j).val < e`.

The cuts lie between zero and `N`, are monotone in `e`, and satisfy `c_s(0)=0` and `c_s(L)=N`. Repeated sample indices contribute once per occurrence.

`FiniteInterval.restrictAlong s` sends `[a,z)` to `[c_s(a),c_s(z))` when those cuts differ, and to `none` otherwise. Its two laws characterize emptiness by the absence of any sampled stage alive in the source interval and identify the alive predicates of a retained interval at every sample stage. `reindexBarcode` applies this restriction by `Multiset.filterMap`. It retains duplicate occurrences, adds multiplicities when different source intervals restrict to the same interval, and drops precisely the empty restrictions. These definitions and interval laws require no coefficient field.

## Actual ranks and endpoint rectangles

`structureMapRank_reindex` identifies the rank of the actual sampled map `i→j` with the rank of the actual source map `s(i)→s(j)`. It follows from the existing structure-map reindexing equation and the linear-map range definition of rank.

For `b < d ≤ N`, define natural endpoints

| Endpoint | Value |
| --- | --- |
| `A` | `0` if `b=0`, otherwise `s(b−1)+1` |
| `B` | `s(b)` |
| `C` | `s(d−1)` |
| `D` | `s(d)` if `d<N`, otherwise `L` |

The integer multiplicity law is

`μ_(reindex s M)(b,d) = ∑_{x∈Icc A B} ∑_{y∈Ioc C D} μ_M(x,y)`.

Each present summand has `x ≤ B ≤ C < y ≤ L`, hence a legal source interval pair. Actual rank transport first expresses the sampled four-rank difference at the rectangle corners. The [finite rank reconstruction](finite-rank-reconstruction.md) rectangle law then telescopes the source multiplicities. If a positive birth follows a repeated sample, `A=B+1`: the birth range is empty and the four-rank terms cancel. A repeated death gives `C=D` and an empty death range. Birth zero uses the integer sentinel `r(-1,j)=0`; target death `N` uses the source sentinel `r(i,L)=0`. The predecessor in these rank expressions is integer subtraction.

## Canonical barcode transport

`rankBarcode_reindex` proves the exact multiset equality

`rankBarcode (reindex s M) = reindexBarcode s (rankBarcode M)`.

The proof counts interval occurrences alive at both sampled endpoints, identifies this count with the rank of the source barcode realization, and uses [canonical rank recovery](finite-rank-barcode.md) to recover the actual ranks of `M`. The existing equality criterion for canonical barcodes and supplied-barcode round trip finish the proof. No interval decomposition or module isomorphism for an arbitrary `M` is constructed or assumed.

`barcodeMultiplicity_rankBarcode_reindex` gives the same rectangle sum with natural canonical barcode multiplicities. It follows by casting the integer law and applying canonical multiplicity recovery at each valid source pair. These natural and integer counts are not reduced modulo the coefficient characteristic.

## Terminal and empty observations

Death `L` means survival through the source's last observed stage; death `N` means survival through the sample's last observed stage. A source interval with death less than `L` may acquire death `N` when the sample ends early. Terminal sampled intervals therefore carry no inference of an infinite lifetime.

Intervals already dead before the first sample, born after the last sample, or entirely between sampled stages disappear. When `N=0`, all cuts are zero, all restrictions are empty, and the actual sampled canonical barcode is empty. A map into `Fin 0` exists only for an empty sample, so the empty-source fixture uses `Fin 0 →o Fin 0` without a hidden nonempty assumption.

## Actual-module fixtures

`RankReindexExamples` proves empty-sample and empty-source barcodes, identity sampling of arbitrary supplied barcodes including duplicates, and the following concrete observations over both `ℚ` and `ZMod 2`:

- Sampling identity and zero transitions on `Fin 2` along `[0,0,1]` gives respectively `{[0,3)}` and `{[0,2),[2,3)}`. The sampled rank `0→1` is one in both cases; rank `0→2` distinguishes one from zero. Multiplicities at birth or death at the repeated boundary vanish.
- Constant sampling `[0,0,0]` gives `{[0,3)}` for both source transitions. The zero-transition source's sampled off-diagonal rank is one, since the sampled arrows are source self maps.
- Sampling `[1,1,3,4]` from the eight source occurrences `[0,6)`, two `[1,4)`, `[2,3)`, `[2,5)`, `[3,6)`, `[5,6)`, `[0,1)` gives exactly `[0,4)`, two `[0,3)`, and two `[2,4)`. The fixtures check all three empty restrictions and the nonterminal-to-terminal restriction `[2,5)↦[2,4)`. Actual sampled ranks at `(0,1)`, `(0,3)`, `(2,2)`, `(2,3)` are `3,1,5,3`. Integer and natural block laws at `(0,3)`, `(2,4)`, `(1,4)`, `(0,1)` give `2,2,0,0`; the `(2,4)` rectangle has births `[2,3]` and deaths `(4,6]`.
- An actual constant module with carrier `k × k` and identity maps, constructed independently of `barcodeModule`, samples along `[0,0,1]` to two copies of `[0,3)` and has sampled off-diagonal rank two. The multiplicity remains two in characteristic two.

## Source correspondence and scope

[Chazal–Crawley-Boevey–de Silva, *The observable structure of persistence modules*, §1.1, p.1](https://arxiv.org/pdf/1405.5644v1) supplies the discrete closed-interval convention and four-rank multiplicity formula. The library's half-open `[b,d)` translates their `[p,q]` by `p=b`, `q=d−1`. The finite cut, rectangle, and canonical transport proofs here are library constructions using the existing finite rank laws.

[Leygonie–Oudot–Tillmann, *A Framework for Differential Calculus on Persistence Barcodes*, Lemma 4.6](https://doi.org/10.1007/s10208-021-09522-y) describes inverse-image restriction of a supplied interval decomposition under a continuous increasing real map, in the proof of its ordering-equivalent barcode-template result, Proposition 4.5. This provides context for finite interval restriction; the present result concerns arbitrary finite-dimensional modules on finite indices and proves canonical barcode equality directly from ranks. It makes no claim about real-index topology, ordering-equivalent filter functions, or template reconstruction.
