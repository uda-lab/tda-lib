# Nonnegative four-rank difference without decomposition

Let `M` be a persistence module on `Fin N` over a field, with each fiber finite
dimensional. For `0 ≤ i ≤ j < N`, let `r(i,j)` be the dimension of the image of
the structure map `M(i → j)`. The auxiliary integer extension
`moduleRankInteger` is zero unless `0 ≤ i ≤ j < N`. Thus `r(-1,j) = 0` and
`r(i,N) = 0`; an invalid pair does not represent a reverse structure map.

For natural `b < d ≤ N`, `moduleMultiplicityInteger` is the integer difference

```text
r(b,d-1) - r(b-1,d-1) - r(b,d) + r(b-1,d).
```

The predecessor calculations occur in integers. The terminal endpoint `d=N`
means survival through the last observed stage, not an infinite lifetime.
The formula is nonnegative for every such module, with no interval-decomposition
assumption.

To see why, take `a ≤ b ≤ c ≤ d` and put `U = im M(a → c)` and
`W = im M(b → c)`. Functoriality gives `U ⊆ W`. Restrict `g = M(c → d)` to
each image. Its range is the corresponding image at `d`, so rank-nullity gives

```text
r(a,c) = r(a,d) + dim ker(g|U),
r(b,c) = r(b,d) + dim ker(g|W).
```

The two kernels identify inside the common ambient fiber at `c` with
`U ∩ ker g` and `W ∩ ker g`. Their dimensions are ordered by `U ⊆ W`.
Subtracting the rank-drop equations proves the four-rank inequality. Interior
endpoints follow by taking `a=b-1`, `c=d-1`. At `b=0`, the negative-source
terms vanish and ordinary rank drop applies. At `d=N`, the terminal terms
vanish and monotonicity in the source applies. For `N=0` no admissible pair
exists.

The genuine fixtures check zero and one-stage boundaries, identity and zero
two-stage transitions, and two three-stage modules
`k → k × k → k`. Both three-stage modules use `x ↦ (x,0)` first. Projection
onto the first coordinate yields `μ(1,2)=1`; projection onto the second gives
`μ(1,2)=0` and `μ(0,2)=1`, because the long composite is zero. These
calculations exercise the functor maps over `ℚ` and `ZMod 2`.

The closed interval `[p,q]` four-rank formula in
[Chazal–Crawley-Boevey–de Silva, §1.1](https://arxiv.org/pdf/1405.5644)
uses `p=b`, `q=d-1` for this library's half-open `[b,d)` convention.
The image-and-kernel proof above is a finite-dimensional linear-algebra
argument; it does not use the paper's decomposition statement.
