# Relabeling finite index bars as value diagrams

Let `v : Fin N → α` be strictly increasing, where `α` is any linearly ordered type, and let `B : Multiset (FiniteInterval N)`. `TDA.Persistence.ofIndexBars v hv B` stores precisely `B.map` of the point function below. For an interval `I`, its birth index is a valid `Fin N` because `I.birth < I.death ≤ N`:

```text
(v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
 if I.death < N then (v ⟨I.death, …⟩ : WithTop α) else ⊤)
```

The second branch means `I.death = N` and uses a **chosen constant-tail extension**. It does not deduce infinite lifetime from finite observations. No grade value at `N`, default element of `α`, filtration, or inhabitedness assumption is involved. The map preserves each occurrence, including duplicates; with `N = 0` the interval type and every such barcode are empty.

Every image point has birth strictly below death. At a finite death this follows from `I.birth < I.death` and strict monotonicity of `v`; at death `N` every finite birth is below `⊤`. Thus `ofIndexBars_isPositive` proves positivity of this image while the ambient [Diagram](finite-diagram-ordered-q.md) still admits reversed finite points. There is no filtering or deletion of bars.

For every `b,d : Fin N`, without an ordering premise, `ofIndexBars_count_finite` identifies the count of `(v b, v d)` with `barcodeMultiplicity B b.val d.val`. Diagonal and reversed pairs both have count zero. `ofIndexBars_count_essential` identifies the count of `(v b, ⊤)` with `barcodeMultiplicity B b.val N`. Point equality reflects equality of both indices by strict monotonicity; finite and top deaths cannot coincide. This makes the point function injective, and `Multiset.map_injective` proves `ofIndexBars_injective` for fixed `v` and `N`, including all multiplicities. It does not assert surjectivity onto positive diagrams.

For **any** `i,j : Fin N`, `ofIndexBars_countP_grades` gives

```text
points.countP (fun p => p.1 ≤ v i ∧ (v j : WithTop α) < p.2)
  = B.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death).
```

Strict monotonicity reflects the finite endpoint inequalities. For death `N`, the right death inequality holds because `j.val < N`, matching the left inequality against `⊤`. The identity is a crossing count even when `i > j`; only `i ≤ j` admits its use as a structure-map rank. Combined with `rank_barcodeMap`, it describes the rank of `barcodeModule B`. With `B = gradeHomologyBarcode k f n` and `v = f.criticalValue`, `rank_gradeHomologyMap` makes the same count the rank of the **actual inclusion-induced simplicial homology map** between observed critical grades. The product fixtures also apply `sublevel_eq_self_of_last_le`, `gradeFiltration_apply`, and `sublevel_bot` to check the genuine tail and empty-complex dependencies.

The constructor by itself makes no claim about all thresholds of an arbitrary value-indexed filtration. In particular, a bar alive at the last sampled grade could die later under another extension. The [Issue #44](https://github.com/uda-lab/tda-lib/issues/44) application must transport ranks using bottom-before-first, intervening-grade, map-naturality, and constant-tail facts of the actual sublevel filtration. It must not infer a module isomorphism from equal ranks. This bridge and its acceptance fixtures are specified in [Issue #154](https://github.com/uda-lab/tda-lib/issues/154); the existing [finite rank barcode](finite-rank-barcode.md) and [actual critical-grade barcode](finite-grade-homology-barcode.md) supply its inputs.
