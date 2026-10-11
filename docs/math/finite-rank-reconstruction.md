# Finite rank reconstruction by rectangular telescoping

Let `M` be a persistence module on `Fin N` over a field, with every fiber finite dimensional. Write `r(i,j)` for the integer cast of the rank of its actual structure map when `0 ≤ i ≤ j < N`; `moduleRankInteger` extends this value by zero outside those bounds. In particular, `r(-1,j)=0` and `r(i,N)=0`. The endpoint `N` denotes survival through the last observed stage, not infinity.

The existing `moduleMultiplicityInteger M b d` is the integer four-rank difference

```text
μ(b,d) = r(b,d-1) - r(b-1,d-1) - r(b,d) + r(b-1,d).
```

Both predecessor operations in this formula are in integers. For `a ≤ b ≤ c ≤ d ≤ N`, the theorem `moduleMultiplicityInteger_sum_rectangle` proves

```text
∑_{x=a}^b ∑_{c<y≤d} μ(x,y)
  = r(b,c) - r(a-1,c) - r(b,d) + r(a-1,d).
```

For each fixed birth, the death sum telescopes the difference `r(x,t)-r(x-1,t)` from `t=c` to `t=d`. The remaining birth differences telescope from `x=a` to `x=b`. This is finite algebraic cancellation. It also covers an empty death interval `c=d`, a single birth `a=b`, and `N=0`, without a positive-size assumption.

Taking `a=0`, `b=i`, `c=j`, and `d=N` makes the three sentinel terms zero. `structureMapRank_eq_sum_moduleMultiplicityInteger` therefore recovers every actual map rank:

```text
rank M(i → j) = ∑_{b≤i} ∑_{j<d≤N} μ(b,d),  for i≤j in Fin N.
```

The sums and equality are in integers. Genuine fixtures check one-stage modules, identity and zero transitions on `Fin 2`, and a constant rank-two module over both `ℚ` and `ZMod 2`. The transition fixtures distinguish modules with equal stage dimensions, while the rank-two fixture verifies that multiplicity is an integer count even in characteristic two.

The half-open four-rank convention translates the closed discrete interval formula in [Chazal–Crawley-Boevey–de Silva, §1.1](https://arxiv.org/pdf/1405.5644), as described in [finite-interval-rank.md](finite-interval-rank.md). The telescoping proof here is a library construction. It reconstructs ranks numerically; it supplies no interval decomposition, barcode object, natural isomorphism, homology finite-dimensionality result, or reducer correctness theorem.
