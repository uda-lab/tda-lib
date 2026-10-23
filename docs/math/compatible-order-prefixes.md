# Prefix complexes from compatible face orders

Let `K` be a preabstract simplicial complex, `f : FilterFunction K α`, and let `e` be a
`CompatibleOrder f` with a finite type of faces of cardinality `m`. For a natural
number `k`, `prefixComplex e k` consists of precisely the faces of `K` whose inverse
enumeration index has value below `k`. The stage is a face count, not a grade or a critical
value.

Proper faces occur before their cofaces, so every prefix is again a preabstract simplicial
complex. The prefixes form a monotone filtration indexed by `ℕ`; stage zero is bottom, stage
`m` is all of `K`, and every later stage remains `K`. If `K` has no faces, then `m = 0` and
every prefix is bottom. Prefix membership always requires membership in `K`, so no absent
ambient vertex is added.

For a grade `r`, define its face count by

```text
cₑ(r) = card { i : Fin m | f.value (e.enum i) ≤ r }.
```

The values along `e.enum` are nondecreasing. Thus the accepted indices are an initial segment:
`f.value (e.enum i) ≤ r` holds exactly when `i.val < cₑ(r)`. The count is monotone in `r`
and bounded by `m`, and the sublevel is recovered as

```text
f.sublevel r = prefixComplex e (cₑ(r)).
```

Consequently, `thresholdMap e : α →o ℕ` reindexes `prefixFiltration e` to the original
sublevel filtration. This construction works for any supplied `CompatibleOrder`; it does not
depend on the implementation of `ofLex`.

Equal grades enter a recovered sublevel together. A face-count stage between the first and
last faces of a tied block can split that block, so the theorem does not say that every prefix
is a grade sublevel. The constant-grade edge fixture demonstrates this distinction.

The lower-set proof uses the support-aware face membership and proper-face order in
[CompatibleOrder](../../TDA/Filtration/CompatibleOrder.lean), while recovery uses the sublevel convention in [FilterFunction](../../TDA/Filtration/FilterFunction.lean) and
reindexing from [Filtration.Basic](../../TDA/Filtration/Basic.lean). The finite count argument
uses the pinned mathlib `Fin.card_Iic` and `Fin.card_Iio` formulas in
[`Order/Interval/Finset/Fin.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/Interval/Finset/Fin.lean).

The API assumes a linear order on grades and a `Fintype` of faces. It requires no
inhabited grade type, vertex order, or vertex decidability. It makes no claim about homology,
barcodes, or invariance under changing the compatible order.
