# Recovering ordinary slice barcodes from signed hooks

Let $M$ be an originally finitely presented persistence module on
$\mathbb R^n$, over an arbitrary field, with $n\ge1$. Choose a positive
affine line $L(t)=b+ta$, where every $a_i>0$. Its entrance time
$\tau_L(p)=\max_i((p_i-b_i)/a_i)$ determines the restrictions of hooks:
a finite hook becomes $[\tau_L(p),\tau_L(q))$, and a principal hook becomes
$[\tau_L(p),\infty)$. Collapsed finite intervals are omitted and every
remaining occurrence is retained. The [slice presentation construction](positive-affine-slices.md)
derives an original finite presentation of $M\circ L$, so it has the
existing ordinary finite barcode $B_L(M)$.

Write $E(M)$ and $O(M)$ for the even and odd hook multisets in the canonical
signed hook barcode of $M$. Applying the endpoint operation to each
multiset gives the exact identity

$$B_L(M)+\operatorname{slice}_L(O(M))
  =\operatorname{slice}_L(E(M)).$$

These are equalities of multisets of real interval endpoints, with infinite
deaths retained. In particular, the odd sliced multiset is contained in the
even one, and removing its occurrences recovers the ordinary barcode.
`finitelyPresented_sliceSignedHookBarcode_cancel` proves the additive
identity from the original finite presentation alone. The accompanying
domination and subtraction theorems make the removal precise.

## Rank counts determine the endpoints

For a finite multiset $D$ of positive intervals and $s\le t$, define

$$\rho_D(s,t)=\#\{[u,v)\in D:u\le s,\ t<v\}.$$

The count includes multiplicities; $t<\infty$ holds for every real $t$.
The rank of the actual structure map of the interval realization is this
count. `RealBarcodeRankUniqueness` reuses the existing interval and
realization rank formulas and proves that equality of all these counts
determines a positive finite endpoint multiset.

The proof places every birth and every finite death from the two multisets
in a common finite ordered grid. Each occurrence becomes a finite index bar,
with essential deaths represented by the terminal index. Finite-barcode
uniqueness then gives equality of the index bars, and mapping back gives
equality of the original real endpoints. This preserves repeated endpoints
and also covers the empty grid.

## Applying a rank-exact resolution

In a finite rank-exact resolution, the rank of each projective term is the
sum of the ranks of its two adjacent kernels, for every comparable pair of
parameters. Evaluate these equations at $L(s)\le L(t)$ and telescope them.
The terminal zero kernel yields

$$\operatorname{rank} M(L(s)\le L(t))
  +\sum_{j\ \mathrm{odd}}\operatorname{rank} Q_j(L(s)\le L(t))
  =\sum_{j\ \mathrm{even}}\operatorname{rank} Q_j(L(s)\le L(t)).$$

Each term's actual finite hook-sum presentation converts its rank into the
corresponding sliced endpoint count. Omitted hooks contribute zero. The
ordinary barcode realization supplies the count for the first term.
Endpoint-count uniqueness proves the displayed multiset identity.

`RankExactBarcodeCancellation` provides the finite-resolution argument;
`AffineSliceRank` supplies its hook-sum and parity comparisons.
`AffineSliceSignedBarcode` obtains the ambient resolution and the ordinary
slice realization internally from the original finite presentation. The
proof uses rank exactness, without assuming that restriction preserves
minimality or projectivity of the resolution.

The cancellation mechanism corresponds to [Botnan, Oppermann and Oudot,
§5.3, Corollaries 5.8–5.9](https://arxiv.org/html/2107.06800v3#S5.SS3).
The source's Corollary 5.8 is stated for rectangles; the hook comparison here
uses the direct support calculation above. The identity recovers the
ordinary slice barcode. Distance comparisons use that ordinary barcode;
common-summand cancellation is not asserted to preserve bottleneck distance.
